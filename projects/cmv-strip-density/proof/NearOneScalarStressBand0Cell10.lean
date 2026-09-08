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
namespace Band0Cell10
def wholeBox : Box3 := { t := ⟨(37 / 2021344 : ℚ), (75 / 4042688 : ℚ), by norm_num⟩, e4 := ⟨(-1 / 8192 : ℚ), (1 / 8192 : ℚ), by norm_num⟩, e3 := ⟨(-1 / 1024 : ℚ), (1 / 1024 : ℚ), by norm_num⟩ }
def centerBox : Box3 := { t := ⟨(149 / 8085376 : ℚ), (149 / 8085376 : ℚ), by norm_num⟩, e4 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩, e3 := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩ }
def aAt (t e4 : ℝ) : ℝ := ((491838928142993121175353635602441465 / 1329227995784915872903807060280344576 : ℚ) : ℝ) + ((-664619210501335092600179162874332053 / 1329227995784915872903807060280344576 : ℚ) : ℝ) * t + t ^ 2 * e4
def bAt (t e3 : ℝ) : ℝ := ((491838928095393980932283885614535351 / 664613997892457936451903530140172288 : ℚ) : ℝ) + ((-387691545295211161336227264168697623 / 664613997892457936451903530140172288 : ℚ) : ℝ) * t + t ^ 2 * e3

def tCenter : ℚ := (149 / 8085376 : ℚ)
def tDisp : LeanSuffixReflective.QInterval := ⟨(-1 / 8085376 : ℚ), (1 / 8085376 : ℚ), by norm_num⟩
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
private abbrev wQ4_wJ3v : LeanSuffixReflective.QInterval := ⟨(469042394751318370847343372375 / 1267650600228229401496703205376 : ℚ), (58630318941973744482289192173 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d0 : LeanSuffixReflective.QInterval := ⟨(-158457569246723053990996627805 / 316912650057057350374175801344 : ℚ), (-633830265503752415612893300781 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d1 : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ4_wJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ3 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (491838928142993121175353635602441465 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-664619210501335092600179162874332053 / 1329227995784915872903807060280344576 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ1))).widenAll wQ4_wJ3v wQ4_wJ3d0 wQ4_wJ3d1 wQ4_wJ3d2 (by
    norm_num [wJ0, wJ1, wQ4_wJ3v, wQ4_wJ3d0, wQ4_wJ3d1, wQ4_wJ3d2])
private abbrev wQ5_wJ4v : LeanSuffixReflective.QInterval := ⟨(938094588540294699991693948817 / 1267650600228229401496703205376 : ℚ), (938094771454826767202057599465 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d0 : LeanSuffixReflective.QInterval := ⟨(-739462984804345626682516274689 / 1267650600228229401496703205376 : ℚ), (-184865723234806805968442647797 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ5_wJ4d2 : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ4 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (491838928095393980932283885614535351 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-387691545295211161336227264168697623 / 664613997892457936451903530140172288 : ℚ)).mul (wJ0))).add (((wJ0).mul (wJ0)).mul (wJ2))).widenAll wQ5_wJ4v wQ5_wJ4d0 wQ5_wJ4d1 wQ5_wJ4d2 (by
    norm_num [wJ0, wJ2, wQ5_wJ4v, wQ5_wJ4d0, wQ5_wJ4d1, wQ5_wJ4d2])
private abbrev wQ6_wJ5v : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d0 : LeanSuffixReflective.QInterval := ⟨(23203904040304118376376321 / 633825300114114700748351602688 : ℚ), (47034940622238077789952003 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ6_wJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ5 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ6_wJ5v wQ6_wJ5d0 wQ6_wJ5d1 wQ6_wJ5d2 (by
    norm_num [wJ0, wQ6_wJ5v, wQ6_wJ5d0, wQ6_wJ5d1, wQ6_wJ5d2])
private abbrev wQ7_wJ6v : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d0 : LeanSuffixReflective.QInterval := ⟨(23203904040304118376376321 / 633825300114114700748351602688 : ℚ), (47034940622238077789952003 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ7_wJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ6 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ7_wJ6v wQ7_wJ6d0 wQ7_wJ6d1 wQ7_wJ6d2 (by
    norm_num [wJ0, wQ7_wJ6v, wQ7_wJ6d0, wQ7_wJ6d1, wQ7_wJ6d2])
private abbrev wQ8_wJ7v : LeanSuffixReflective.QInterval := ⟨(86775002526107098209277114149 / 633825300114114700748351602688 : ℚ), (173550121075629938104570006247 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d0 : LeanSuffixReflective.QInterval := ⟨(-234523117257265798617926627639 / 633825300114114700748351602688 : ℚ), (-469046069231093993324147710999 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d1 : LeanSuffixReflective.QInterval := ⟨(314314982391885477271 / 1267650600228229401496703205376 : ℚ), (322867488484699267391 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ8_wJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ7 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ3).mul (wJ3)).widenAll wQ8_wJ7v wQ8_wJ7d0 wQ8_wJ7d1 wQ8_wJ7d2 (by
    norm_num [wJ3, wQ8_wJ7v, wQ8_wJ7d0, wQ8_wJ7d1, wQ8_wJ7d2])
private abbrev wQ9_wJ8v : LeanSuffixReflective.QInterval := ⟨(39614081252087364289198549115 / 39614081257132168796771975168 : ℚ), (1267650600071071910300760466741 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d0 : LeanSuffixReflective.QInterval := ⟨(-17403154579129817062175105 / 1267650600228229401496703205376 : ℚ), (-17171098168133090240186485 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d1 : LeanSuffixReflective.QInterval := ⟨(-75081635261 / 633825300114114700748351602688 : ℚ), (-142313317891 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ9_wJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ8 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ6).mul (wJ3)).neg)).widenAll wQ9_wJ8v wQ9_wJ8d0 wQ9_wJ8d1 wQ9_wJ8d2 (by
    norm_num [wJ6, wJ3, wQ9_wJ8v, wQ9_wJ8d0, wQ9_wJ8d1, wQ9_wJ8d2])
private abbrev wQ10_wJ9v : LeanSuffixReflective.QInterval := ⟨(938084789442904749858943349545 / 1267650600228229401496703205376 : ℚ), (938085103013430192850574599477 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d0 : LeanSuffixReflective.QInterval := ⟨(-1267666993224801988434219620725 / 1267650600228229401496703205376 : ℚ), (-633833442195611438935650903927 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d1 : LeanSuffixReflective.QInterval := ⟨(849478811502587234881 / 1267650600228229401496703205376 : ℚ), (109074103240285370323 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ10_wJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ9 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add (((wJ6).mul (wJ7)).neg)).widenAll wQ10_wJ9v wQ10_wJ9d0 wQ10_wJ9d1 wQ10_wJ9d2 (by
    norm_num [wJ3, wJ6, wJ7, wQ10_wJ9v, wQ10_wJ9d0, wQ10_wJ9d1, wQ10_wJ9d2])
private abbrev wQ11_wJ10v : LeanSuffixReflective.QInterval := ⟨(469065598625492679119004710039 / 633825300114114700748351602688 : ℚ), (938132137954052431078527822001 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d0 : LeanSuffixReflective.QInterval := ⟨(633817103615843956694254980227 / 633825300114114700748351602688 : ℚ), (1267634316065268301828866079325 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d1 : LeanSuffixReflective.QInterval := ⟨(849478811502587234881 / 1267650600228229401496703205376 : ℚ), (109074103240285370323 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ11_wJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ10 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ6).mul (wJ7)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ11_wJ10v wQ11_wJ10d0 wQ11_wJ10d1 wQ11_wJ10d2 (by
    norm_num [wJ3, wJ0, wJ6, wJ7, wQ11_wJ10v, wQ11_wJ10d0, wQ11_wJ10d1, wQ11_wJ10d2])
private abbrev wQ11_root11 : LeanSuffixReflective.QInterval := ⟨(545243923946491677442746222761 / 633825300114114700748351602688 : ℚ), (1090488030149866062086172147281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11v : LeanSuffixReflective.QInterval := ⟨(545243923946491677442746222761 / 633825300114114700748351602688 : ℚ), (1090488030149866062086172147281 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d0 : LeanSuffixReflective.QInterval := ⟨(-736807305077202633096696748611 / 1267650600228229401496703205376 : ℚ), (-46050444917169861306369749387 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d1 : LeanSuffixReflective.QInterval := ⟨(30858956480660169459 / 79228162514264337593543950336 : ℚ), (507177967032137830075 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ12_wJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ11 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ9).sqrt wQ11_root11 (by norm_num [wQ11_root11]) (by norm_num [wJ9, wQ11_root11]) (by norm_num [wJ9, wQ11_root11])).widenAll wQ12_wJ11v wQ12_wJ11d0 wQ12_wJ11d1 wQ12_wJ11d2 (by
    norm_num [wJ9, wQ11_root11, NearOneScalarInterval.Jet3.sqrt, wQ12_wJ11v, wQ12_wJ11d0, wQ12_wJ11d1, wQ12_wJ11d2])
private abbrev wQ12_root12 : LeanSuffixReflective.QInterval := ⟨(1090514821214291915886617998867 / 1267650600228229401496703205376 : ℚ), (1090515367966378854854019834011 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12v : LeanSuffixReflective.QInterval := ⟨(1090514821214291915886617998867 / 1267650600228229401496703205376 : ℚ), (1090515367966378854854019834011 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d0 : LeanSuffixReflective.QInterval := ⟨(92096206921394974205082898749 / 158456325028528675187087900672 : ℚ), (184192522005424293516589300457 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d1 : LeanSuffixReflective.QInterval := ⟨(493730926181508543787 / 1267650600228229401496703205376 : ℚ), (253582711123434146635 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ13_wJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ12 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ10).sqrt wQ12_root12 (by norm_num [wQ12_root12]) (by norm_num [wJ10, wQ12_root12]) (by norm_num [wJ10, wQ12_root12])).widenAll wQ13_wJ12v wQ13_wJ12d0 wQ13_wJ12d1 wQ13_wJ12d2 (by
    norm_num [wJ10, wQ12_root12, NearOneScalarInterval.Jet3.sqrt, wQ13_wJ12v, wQ13_wJ12d0, wQ13_wJ12d1, wQ13_wJ12d2])
private abbrev wQ14_wJ13v : LeanSuffixReflective.QInterval := ⟨(633825300114118588102016998991 / 633825300114114700748351602688 : ℚ), (1267650600228237495673393574483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d0 : LeanSuffixReflective.QInterval := ⟨(1274218217420566286479 / 1267650600228229401496703205376 : ℚ), (327222309760349039511 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ14_wJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ13 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ14_wJ13v wQ14_wJ13d0 wQ14_wJ13d1 wQ14_wJ13d2 (by
    norm_num [wJ0, wQ14_wJ13v, wQ14_wJ13d0, wQ14_wJ13d1, wQ14_wJ13d2])
private abbrev wQ15_wJ14v : LeanSuffixReflective.QInterval := ⟨(272625333638410244863932922003 / 158456325028528675187087900672 : ℚ), (2181003398116251879902062686373 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d0 : LeanSuffixReflective.QInterval := ⟨(-37648609909947977653728597 / 1267650600228229401496703205376 : ℚ), (-37029527061829827189587493 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d1 : LeanSuffixReflective.QInterval := ⟨(493737114936037141669 / 633825300114114700748351602688 : ℚ), (126792923659876170221 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ15_wJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ14 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ12).add ((wJ13).mul (wJ11))).widenAll wQ15_wJ14v wQ15_wJ14d0 wQ15_wJ14d1 wQ15_wJ14d2 (by
    norm_num [wJ12, wJ13, wJ11, wQ15_wJ14v, wQ15_wJ14d0, wQ15_wJ14d1, wQ15_wJ14d2])
private abbrev wQ16_wJ15v : LeanSuffixReflective.QInterval := ⟨(1614022062866778764093304380431 / 1267650600228229401496703205376 : ℚ), (807011840670412315833274558541 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d0 : LeanSuffixReflective.QInterval := ⟨(-111105810729527441416758845 / 1267650600228229401496703205376 : ℚ), (-54501181301052985813113403 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d1 : LeanSuffixReflective.QInterval := ⟨(2192301572705790469301 / 1267650600228229401496703205376 : ℚ), (2251955572003077948035 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ16_wJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ15 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).mul (wJ12)).mul (wJ14)).widenAll wQ16_wJ15v wQ16_wJ15d0 wQ16_wJ15d1 wQ16_wJ15d2 (by
    norm_num [wJ11, wJ12, wJ14, wQ16_wJ15v, wQ16_wJ15d0, wQ16_wJ15d1, wQ16_wJ15d2])
private abbrev wQ17_wJ16v : LeanSuffixReflective.QInterval := ⟨(2181002669107295335355601006477 / 1267650600228229401496703205376 : ℚ), (272625424764533225750045120443 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d0 : LeanSuffixReflective.QInterval := ⟨(-37646417607642899033761075 / 1267650600228229401496703205376 : ℚ), (-37027275107010963676185637 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d1 : LeanSuffixReflective.QInterval := ⟨(493737114936040169839 / 633825300114114700748351602688 : ℚ), (1014343389279015838533 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ17_wJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ16 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ13).mul (wJ14)).widenAll wQ17_wJ16v wQ17_wJ16d0 wQ17_wJ16d1 wQ17_wJ16d2 (by
    norm_num [wJ13, wJ14, wQ17_wJ16v, wQ17_wJ16d0, wQ17_wJ16d1, wQ17_wJ16d2])
private abbrev wQ18_wJ17v : LeanSuffixReflective.QInterval := ⟨(1090501334546286997062013158503 / 633825300114114700748351602688 : ℚ), (2181003398130973500709180498765 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d0 : LeanSuffixReflective.QInterval := ⟨(-19223001931301601679988141 / 633825300114114700748351602688 : ℚ), (-18114955508391093790092433 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d1 : LeanSuffixReflective.QInterval := ⟨(987474229838403100705 / 1267650600228229401496703205376 : ℚ), (507171694656434049615 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ18_wJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ17 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ11).add (wJ12)).mul (((wJ8).mul (wJ8)).add ((wJ6).mul ((wJ11).mul (wJ12))))).widenAll wQ18_wJ17v wQ18_wJ17d0 wQ18_wJ17d1 wQ18_wJ17d2 (by
    norm_num [wJ11, wJ12, wJ8, wJ6, wQ18_wJ17v, wQ18_wJ17d0, wQ18_wJ17d1, wQ18_wJ17d2])
private abbrev wQ19_wJ18v : LeanSuffixReflective.QInterval := ⟨(2535301199810731600772453465783 / 1267650600228229401496703205376 : ℚ), (2535301199827836932425291144271 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d0 : LeanSuffixReflective.QInterval := ⟨(-17402836022418035553238633 / 316912650057057350374175801344 : ℚ), (-17170770943636745458078655 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d1 : LeanSuffixReflective.QInterval := ⟨(-300326541007 / 633825300114114700748351602688 : ℚ), (-569253271491 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ19_wJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ18 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ19_wJ18v wQ19_wJ18d0 wQ19_wJ18d1 wQ19_wJ18d2 (by
    norm_num [wJ8, wJ0, wQ19_wJ18v, wQ19_wJ18d0, wQ19_wJ18d1, wQ19_wJ18d2])
private abbrev wQ20_wJ19v : LeanSuffixReflective.QInterval := ⟨(497804977348303813222967558443 / 633825300114114700748351602688 : ℚ), (497805476526384632571746673807 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d0 : LeanSuffixReflective.QInterval := ⟨(67238070015150870240720925 / 1267650600228229401496703205376 : ℚ), (34267859360499902387556587 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d1 : LeanSuffixReflective.QInterval := ⟨(-1389120808728089230841 / 1267650600228229401496703205376 : ℚ), (-1352320473804751798007 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ20_wJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ19 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ15).invPos (by norm_num [wJ15])).widenAll wQ20_wJ19v wQ20_wJ19d0 wQ20_wJ19d1 wQ20_wJ19d2 (by
    norm_num [wJ15, NearOneScalarInterval.Jet3.invPos, wQ20_wJ19v, wQ20_wJ19d0, wQ20_wJ19d1, wQ20_wJ19d2])
private abbrev wQ21_wJ20v : LeanSuffixReflective.QInterval := ⟨(497804977221515637042199964679 / 316912650057057350374175801344 : ℚ), (995610952805909909910491966855 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d0 : LeanSuffixReflective.QInterval := ⟨(79803490750332730685156123 / 1267650600228229401496703205376 : ℚ), (83127896567273106385428885 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d1 : LeanSuffixReflective.QInterval := ⟨(-2778241617239072159883 / 1267650600228229401496703205376 : ℚ), (-676160236841934186563 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ21_wJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ20 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ19)).widenAll wQ21_wJ20v wQ21_wJ20d0 wQ21_wJ20d1 wQ21_wJ20d2 (by
    norm_num [wJ18, wJ19, wQ21_wJ20v, wQ21_wJ20d0, wQ21_wJ20d1, wQ21_wJ20d2])
private abbrev wQ22_wJ21v : LeanSuffixReflective.QInterval := ⟨(736788418416451718074325593471 / 1267650600228229401496703205376 : ℚ), (736788664690962965840249395277 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d0 : LeanSuffixReflective.QInterval := ⟨(12508585492314368322396053 / 1267650600228229401496703205376 : ℚ), (6358876619551952628272965 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d1 : LeanSuffixReflective.QInterval := ⟨(-85666643364413186171 / 316912650057057350374175801344 : ℚ), (-333589382154492506221 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ22_wJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ21 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ16).invPos (by norm_num [wJ16])).widenAll wQ22_wJ21v wQ22_wJ21d0 wQ22_wJ21d1 wQ22_wJ21d2 (by
    norm_num [wJ16, NearOneScalarInterval.Jet3.invPos, wQ22_wJ21v, wQ22_wJ21d0, wQ22_wJ21d1, wQ22_wJ21d2])
private abbrev wQ23_wJ22v : LeanSuffixReflective.QInterval := ⟨(1473576836457591560804452237433 / 1267650600228229401496703205376 : ℚ), (1473577329016555956288203130015 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d0 : LeanSuffixReflective.QInterval := ⟨(-7721298538038995566647973 / 633825300114114700748351602688 : ℚ), (-14484721276267133761010217 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d1 : LeanSuffixReflective.QInterval := ⟨(-342666573547246312427 / 633825300114114700748351602688 : ℚ), (-41698672779370105785 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ23_wJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ22 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ18).mul (wJ21)).widenAll wQ23_wJ22v wQ23_wJ22d0 wQ23_wJ22d1 wQ23_wJ22d2 (by
    norm_num [wJ18, wJ21, wQ23_wJ22v, wQ23_wJ22d0, wQ23_wJ22d1, wQ23_wJ22d2])
private abbrev wQ24_wJ23v : LeanSuffixReflective.QInterval := ⟨(736788418411483152169132808319 / 1267650600228229401496703205376 : ℚ), (736788664695936145150013708361 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d0 : LeanSuffixReflective.QInterval := ⟨(1529902409833424754647151 / 158456325028528675187087900672 : ℚ), (12987870326911497447118771 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d1 : LeanSuffixReflective.QInterval := ⟨(-342666573473714616393 / 1267650600228229401496703205376 : ℚ), (-333589382138616482713 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ24_wJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ23 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ17).invPos (by norm_num [wJ17])).widenAll wQ24_wJ23v wQ24_wJ23d0 wQ24_wJ23d1 wQ24_wJ23d2 (by
    norm_num [wJ17, NearOneScalarInterval.Jet3.invPos, wQ24_wJ23v, wQ24_wJ23d0, wQ24_wJ23d1, wQ24_wJ23d2])
private abbrev wQ25_wJ24v : LeanSuffixReflective.QInterval := ⟨(368394209158828156519272919841 / 316912650057057350374175801344 : ℚ), (46049291537787176714227491777 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d0 : LeanSuffixReflective.QInterval := ⟨(2124462413682722080941733 / 633825300114114700748351602688 : ℚ), (6016007152755068564906999 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d1 : LeanSuffixReflective.QInterval := ⟨(-685333147037023894537 / 1267650600228229401496703205376 : ℚ), (-333589382178851164241 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ25_wJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ24 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ23)).widenAll wQ25_wJ24v wQ25_wJ24d0 wQ25_wJ24d1 wQ25_wJ24d2 (by
    norm_num [wJ8, wJ0, wJ23, wQ25_wJ24v, wQ25_wJ24d0, wQ25_wJ24d1, wQ25_wJ24d2])
private abbrev wQ26_wJ25v : LeanSuffixReflective.QInterval := ⟨(1267650600385386892712129606967 / 1267650600228229401496703205376 : ℚ), (1267650600389663145759611227779 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d0 : LeanSuffixReflective.QInterval := ⟨(8585549086195338897494543 / 633825300114114700748351602688 : ℚ), (8701577291781178854604279 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d1 : LeanSuffixReflective.QInterval := ⟨(71156658963 / 633825300114114700748351602688 : ℚ), (150163270561 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ26_wJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ25 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ26_wJ25v wQ26_wJ25d0 wQ26_wJ25d1 wQ26_wJ25d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ26_wJ25v, wQ26_wJ25d0, wQ26_wJ25d1, wQ26_wJ25d2])
private abbrev wQ27_wJ26v : LeanSuffixReflective.QInterval := ⟨(4990373779763747577418473 / 316912650057057350374175801344 : ℚ), (20231255196516302616535497 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d0 : LeanSuffixReflective.QInterval := ⟨(136316038491572058897346011913 / 158456325028528675187087900672 : ℚ), (545264518475597626624375523897 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d1 : LeanSuffixReflective.QInterval := ⟨(9037573157023449 / 1267650600228229401496703205376 : ℚ), (9408939468751399 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ27_wJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ26 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ12)).mul (wJ25)).widenAll wQ27_wJ26v wQ27_wJ26d0 wQ27_wJ26d1 wQ27_wJ26d2 (by
    norm_num [wJ0, wJ12, wJ25, wQ27_wJ26v, wQ27_wJ26d0, wQ27_wJ26d1, wQ27_wJ26d2])
private abbrev wQ28_wJ27v : LeanSuffixReflective.QInterval := ⟨(61717139357105087849 / 158456325028528675187087900672 : ℚ), (507171694563684631039 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d0 : LeanSuffixReflective.QInterval := ⟨(421458004526825703550743 / 9903520314283042199192993792 : ℚ), (13668912824199463723722063 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d1 : LeanSuffixReflective.QInterval := ⟨(-58969008045 / 316912650057057350374175801344 : ℚ), (-55886281261 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ28_wJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ27 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ6).mul (wJ24)).widenAll wQ28_wJ27v wQ28_wJ27d0 wQ28_wJ27d1 wQ28_wJ27d2 (by
    norm_num [wJ6, wJ24, wQ28_wJ27v, wQ28_wJ27d0, wQ28_wJ27d1, wQ28_wJ27d2])
private abbrev wQ29_wJ28v : LeanSuffixReflective.QInterval := ⟨(1267650600120601509196601912987 / 1267650600228229401496703205376 : ℚ), (633825300063690844595092592789 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d0 : LeanSuffixReflective.QInterval := ⟨(-11602999574647436809766641 / 1267650600228229401496703205376 : ℚ), (-688682180182110486614223 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d1 : LeanSuffixReflective.QInterval := ⟨(-100109136901 / 1267650600228229401496703205376 : ℚ), (-91317426907 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ29_wJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ28 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ26]) (by norm_num [wJ26])).widenAll wQ29_wJ28v wQ29_wJ28d0 wQ29_wJ28d1 wQ29_wJ28d2 (by
    norm_num [wJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ29_wJ28v, wQ29_wJ28d0, wQ29_wJ28d1, wQ29_wJ28d2])
private abbrev wQ30_wJ29v : LeanSuffixReflective.QInterval := ⟨(158456325028528675178633181113 / 158456325028528675187087900672 : ℚ), (1267650600228229401435005151289 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d0 : LeanSuffixReflective.QInterval := ⟨(-1822922309733305 / 158456325028528675187087900672 : ℚ), (-13482485560679787 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d1 : LeanSuffixReflective.QInterval := ⟨(55 / 1267650600228229401496703205376 : ℚ), (63 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ30_wJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ29 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ27]) (by norm_num [wJ27])).widenAll wQ30_wJ29v wQ30_wJ29d0 wQ30_wJ29d1 wQ30_wJ29d2 (by
    norm_num [wJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ30_wJ29v, wQ30_wJ29d0, wQ30_wJ29d1, wQ30_wJ29d2])
private abbrev wQ31_wJ30v : LeanSuffixReflective.QInterval := ⟨(1267650600385386892712129606967 / 1267650600228229401496703205376 : ℚ), (1267650600389663145759611227779 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d0 : LeanSuffixReflective.QInterval := ⟨(8585549086195338897494543 / 633825300114114700748351602688 : ℚ), (8701577291781178854604279 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d1 : LeanSuffixReflective.QInterval := ⟨(71156658963 / 633825300114114700748351602688 : ℚ), (150163270561 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ31_wJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ30 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ8).invPos (by norm_num [wJ8])).widenAll wQ31_wJ30v wQ31_wJ30d0 wQ31_wJ30d1 wQ31_wJ30d2 (by
    norm_num [wJ8, NearOneScalarInterval.Jet3.invPos, wQ31_wJ30v, wQ31_wJ30d0, wQ31_wJ30d1, wQ31_wJ30d2])
private abbrev wQ32_wJ31v : LeanSuffixReflective.QInterval := ⟨(1473576837000700862410639182629 / 1267650600228229401496703205376 : ℚ), (736788664792260081254804620977 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d0 : LeanSuffixReflective.QInterval := ⟨(44172161908918080913586313 / 1267650600228229401496703205376 : ℚ), (46478771108326357689631039 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d1 : LeanSuffixReflective.QInterval := ⟨(-685333146871594256179 / 1267650600228229401496703205376 : ℚ), (-667178764183147561843 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ32_wJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ31 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ6).mul (wJ12)).mul (wJ30)).mul (wJ28)).add ((wJ24).mul (wJ29))).widenAll wQ32_wJ31v wQ32_wJ31d0 wQ32_wJ31d1 wQ32_wJ31d2 (by
    norm_num [wJ6, wJ12, wJ30, wJ28, wJ24, wJ29, wQ32_wJ31v, wQ32_wJ31d0, wQ32_wJ31d1, wQ32_wJ31d2])
private abbrev wQ33_wJ32v : LeanSuffixReflective.QInterval := ⟨(938094588540294699991693948817 / 633825300114114700748351602688 : ℚ), (938094771454826767202057599465 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d0 : LeanSuffixReflective.QInterval := ⟨(-739462984804345626682516274689 / 633825300114114700748351602688 : ℚ), (-184865723234806805968442647797 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ33_wJ32d2 : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 316912650057057350374175801344 : ℚ), (109074103253449679837 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ32 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ4)).widenAll wQ33_wJ32v wQ33_wJ32d0 wQ33_wJ32d1 wQ33_wJ32d2 (by
    norm_num [wJ4, wQ33_wJ32v, wQ33_wJ32d0, wQ33_wJ32d1, wQ33_wJ32d2])
private abbrev wQ34_wJ33v : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d0 : LeanSuffixReflective.QInterval := ⟨(23203904040304118376376321 / 633825300114114700748351602688 : ℚ), (47034940622238077789952003 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ34_wJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ33 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ0).mul (wJ0)).widenAll wQ34_wJ33v wQ34_wJ33d0 wQ34_wJ33d1 wQ34_wJ33d2 (by
    norm_num [wJ0, wQ34_wJ33v, wQ34_wJ33d0, wQ34_wJ33d1, wQ34_wJ33d2])
private abbrev wQ35_wJ34v : LeanSuffixReflective.QInterval := ⟨(1388429046442520749994350832573 / 633825300114114700748351602688 : ℚ), (2776859175777437215967738089695 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d0 : LeanSuffixReflective.QInterval := ⟨(-4377776397404423511831924167195 / 1267650600228229401496703205376 : ℚ), (-547221874992800249925592999799 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ35_wJ34d2 : LeanSuffixReflective.QInterval := ⟨(1257273062642007604505 / 633825300114114700748351602688 : ℚ), (2582966528972899020697 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ34 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ32).mul (wJ32)).widenAll wQ35_wJ34v wQ35_wJ34d0 wQ35_wJ34d1 wQ35_wJ34d2 (by
    norm_num [wJ32, wQ35_wJ34v, wQ35_wJ34d0, wQ35_wJ34d1, wQ35_wJ34d2])
private abbrev wQ36_wJ35v : LeanSuffixReflective.QInterval := ⟨(1267650599582487769253478450201 / 1267650600228229401496703205376 : ℚ), (316912649899898217543924850781 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d0 : LeanSuffixReflective.QInterval := ⟨(-69613689744533814730479535 / 1267650600228229401496703205376 : ℚ), (-34342736865780916678761807 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ36_wJ35d2 : LeanSuffixReflective.QInterval := ⟨(-300326541043 / 1267650600228229401496703205376 : ℚ), (-142313317891 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ35 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ33).mul (wJ32)).neg)).widenAll wQ36_wJ35v wQ36_wJ35d0 wQ36_wJ35d1 wQ36_wJ35d2 (by
    norm_num [wJ33, wJ32, wQ36_wJ35v, wQ36_wJ35d0, wQ36_wJ35d1, wQ36_wJ35d2])
private abbrev wQ37_wJ36v : LeanSuffixReflective.QInterval := ⟨(469047294150680903798248894151 / 158456325028528675187087900672 : ℚ), (1876189542444446064707969335603 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d0 : LeanSuffixReflective.QInterval := ⟨(-1478977485202582796409571139123 / 633825300114114700748351602688 : ℚ), (-2957953229096407928153459818657 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ37_wJ36d2 : LeanSuffixReflective.QInterval := ⟨(1698957622338423570765 / 1267650600228229401496703205376 : ℚ), (1745185651212670267745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ36 : NearOneScalarInterval.Jet3 wholeBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add (((wJ33).mul (wJ34)).neg)).widenAll wQ37_wJ36v wQ37_wJ36d0 wQ37_wJ36d1 wQ37_wJ36d2 (by
    norm_num [wJ32, wJ33, wJ34, wQ37_wJ36v, wQ37_wJ36d0, wQ37_wJ36d1, wQ37_wJ36d2])
private abbrev wQ38_wJ37v : LeanSuffixReflective.QInterval := ⟨(3752424761013527838765057223741 / 1267650600228229401496703205376 : ℚ), (1876213059914757183821945946865 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d0 : LeanSuffixReflective.QInterval := ⟨(-422653769948675690996412697067 / 1267650600228229401496703205376 : ℚ), (-422652028639916748453291931477 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ38_wJ37d2 : LeanSuffixReflective.QInterval := ⟨(1698957622338423570765 / 1267650600228229401496703205376 : ℚ), (1745185651212670267745 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ37 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ0))).add (((wJ33).mul (wJ34)).neg)).add (((wJ0).mul (wJ0)).mul ((wJ0).mul (wJ0)))).widenAll wQ38_wJ37v wQ38_wJ37d0 wQ38_wJ37d1 wQ38_wJ37d2 (by
    norm_num [wJ32, wJ0, wJ33, wJ34, wQ38_wJ37v, wQ38_wJ37d0, wQ38_wJ37d1, wQ38_wJ37d2])
private abbrev wQ38_root38 : LeanSuffixReflective.QInterval := ⟨(272623385819507769838165802411 / 158456325028528675187087900672 : ℚ), (1090493649596738627647195846795 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38v : LeanSuffixReflective.QInterval := ⟨(272623385819507769838165802411 / 158456325028528675187087900672 : ℚ), (1090493649596738627647195846795 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d0 : LeanSuffixReflective.QInterval := ⟨(-859623015834348466121786376693 / 1267650600228229401496703205376 : ℚ), (-107452803247000250182501105897 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ39_wJ38d2 : LeanSuffixReflective.QInterval := ⟨(493740759177289667935 / 1267650600228229401496703205376 : ℚ), (507175317980170943771 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ38 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ36).sqrt wQ38_root38 (by norm_num [wQ38_root38]) (by norm_num [wJ36, wQ38_root38]) (by norm_num [wJ36, wQ38_root38])).widenAll wQ39_wJ38v wQ39_wJ38d0 wQ39_wJ38d1 wQ39_wJ38d2 (by
    norm_num [wJ36, wQ38_root38, NearOneScalarInterval.Jet3.sqrt, wQ39_wJ38v, wQ39_wJ38d0, wQ39_wJ38d1, wQ39_wJ38d2])
private abbrev wQ39_root39 : LeanSuffixReflective.QInterval := ⟨(2181000573271375559427950313683 / 1267650600228229401496703205376 : ℚ), (2181000968159796519933537137601 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39v : LeanSuffixReflective.QInterval := ⟨(2181000573271375559427950313683 / 1267650600228229401496703205376 : ℚ), (2181000968159796519933537137601 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d0 : LeanSuffixReflective.QInterval := ⟨(-61414163724923688236706975667 / 633825300114114700748351602688 : ℚ), (-15353474895666986928558989963 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ40_wJ39d2 : LeanSuffixReflective.QInterval := ⟨(61717208095074335917 / 158456325028528675187087900672 : ℚ), (507172181745723594565 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ39 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ37).sqrt wQ39_root39 (by norm_num [wQ39_root39]) (by norm_num [wJ37, wQ39_root39]) (by norm_num [wJ37, wQ39_root39])).widenAll wQ40_wJ39v wQ40_wJ39d0 wQ40_wJ39d1 wQ40_wJ39d2 (by
    norm_num [wJ37, wQ39_root39, NearOneScalarInterval.Jet3.sqrt, wQ40_wJ39v, wQ40_wJ39d0, wQ40_wJ39d1, wQ40_wJ39d2])
private abbrev wQ41_wJ40v : LeanSuffixReflective.QInterval := ⟨(633825300114118588102016998991 / 633825300114114700748351602688 : ℚ), (1267650600228237495673393574483 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d0 : LeanSuffixReflective.QInterval := ⟨(1274218217420566286479 / 1267650600228229401496703205376 : ℚ), (327222309760349039511 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ41_wJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ40 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0))).widenAll wQ41_wJ40v wQ41_wJ40d0 wQ41_wJ40d1 wQ41_wJ40d2 (by
    norm_num [wJ0, wQ41_wJ40v, wQ41_wJ40d0, wQ41_wJ40d1, wQ41_wJ40d2])
private abbrev wQ42_wJ41v : LeanSuffixReflective.QInterval := ⟨(1090496914956862773620461010523 / 316912650057057350374175801344 : ℚ), (4361988267353287701223432595869 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d0 : LeanSuffixReflective.QInterval := ⟨(-61403208818244668087932298999 / 79228162514264337593543950336 : ℚ), (-982450222889404972647711267367 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ42_wJ41d2 : LeanSuffixReflective.QInterval := ⟨(987478423937887383463 / 1267650600228229401496703205376 : ℚ), (507173749862948888371 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ41 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ39).add ((wJ40).mul (wJ38))).widenAll wQ42_wJ41v wQ42_wJ41d0 wQ42_wJ41d1 wQ42_wJ41d2 (by
    norm_num [wJ39, wJ40, wJ38, wQ42_wJ41v, wQ42_wJ41d0, wQ42_wJ41d1, wQ42_wJ41d2])
private abbrev wQ43_wJ42v : LeanSuffixReflective.QInterval := ⟨(12912019513554484318750804359927 / 1267650600228229401496703205376 : ℚ), (12912024908605277789013458331331 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d0 : LeanSuffixReflective.QInterval := ⟨(-4362273109355859984670869354497 / 633825300114114700748351602688 : ℚ), (-4362266838251127192965895625791 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ43_wJ42d2 : LeanSuffixReflective.QInterval := ⟨(4384586227750132002879 / 633825300114114700748351602688 : ℚ), (2251945565850802980823 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ42 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).mul (wJ39)).mul (wJ41)).widenAll wQ43_wJ42v wQ43_wJ42d0 wQ43_wJ42d1 wQ43_wJ42d2 (by
    norm_num [wJ38, wJ39, wJ41, wQ43_wJ42v, wQ43_wJ42d0, wQ43_wJ42d1, wQ43_wJ42d2])
private abbrev wQ44_wJ43v : LeanSuffixReflective.QInterval := ⟨(4361987659827477847261694879221 / 1267650600228229401496703205376 : ℚ), (2180994133676657776650859464769 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d0 : LeanSuffixReflective.QInterval := ⟨(-245612834176833530468704108831 / 316912650057057350374175801344 : ℚ), (-982450218385520491645869006961 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ44_wJ43d2 : LeanSuffixReflective.QInterval := ⟨(246869605984473359957 / 316912650057057350374175801344 : ℚ), (1014347499725904253533 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ43 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ40).mul (wJ41)).widenAll wQ44_wJ43v wQ44_wJ43d0 wQ44_wJ43d1 wQ44_wJ43d2 (by
    norm_num [wJ40, wJ41, wQ44_wJ43v, wQ44_wJ43d0, wQ44_wJ43d1, wQ44_wJ43d2])
private abbrev wQ45_wJ44v : LeanSuffixReflective.QInterval := ⟨(1090496914927436778459708415323 / 316912650057057350374175801344 : ℚ), (1090497066867754750151665789171 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d0 : LeanSuffixReflective.QInterval := ⟨(-982457726872722528490592879901 / 1267650600228229401496703205376 : ℚ), (-491221916332191262231545739705 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ45_wJ44d2 : LeanSuffixReflective.QInterval := ⟨(61717401487699634859 / 79228162514264337593543950336 : ℚ), (1014347499861322402295 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ44 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ38).add (wJ39)).mul (((wJ35).mul (wJ35)).add ((wJ33).mul ((wJ38).mul (wJ39))))).widenAll wQ45_wJ44v wQ45_wJ44d0 wQ45_wJ44d1 wQ45_wJ44d2 (by
    norm_num [wJ38, wJ39, wJ35, wJ33, wQ45_wJ44v, wQ45_wJ44d0, wQ45_wJ44d1, wQ45_wJ44d2])
private abbrev wQ46_wJ45v : LeanSuffixReflective.QInterval := ⟨(633825299468375012346428065257 / 316912650057057350374175801344 : ℚ), (2535301197941920772509563782977 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d0 : LeanSuffixReflective.QInterval := ⟨(-278453484621832421743345837 / 1267650600228229401496703205376 : ℚ), (-274740585897056821184447675 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ46_wJ45d2 : LeanSuffixReflective.QInterval := ⟨(-1201306163577 / 1267650600228229401496703205376 : ℚ), (-284626635637 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ45 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul (wJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).widenAll wQ46_wJ45v wQ46_wJ45d0 wQ46_wJ45d1 wQ46_wJ45d2 (by
    norm_num [wJ35, wJ0, wQ46_wJ45v, wQ46_wJ45d0, wQ46_wJ45d1, wQ46_wJ45d2])
private abbrev wQ47_wJ46v : LeanSuffixReflective.QInterval := ⟨(124452830259647276511119286439 / 1267650600228229401496703205376 : ℚ), (124452882259982308307828355497 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d0 : LeanSuffixReflective.QInterval := ⟨(42045802901630085920187723671 / 633825300114114700748351602688 : ℚ), (1313934327562589307481523699 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ47_wJ46d2 : LeanSuffixReflective.QInterval := ⟨(-86821775964174502421 / 1267650600228229401496703205376 : ℚ), (-84521857636335150065 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ46 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ42).invPos (by norm_num [wJ42])).widenAll wQ47_wJ46v wQ47_wJ46d0 wQ47_wJ46d1 wQ47_wJ46d2 (by
    norm_num [wJ42, NearOneScalarInterval.Jet3.invPos, wQ47_wJ46v, wQ47_wJ46d0, wQ47_wJ46d1, wQ47_wJ46d2])
private abbrev wQ48_wJ47v : LeanSuffixReflective.QInterval := ⟨(248905660265710065883169639613 / 1267650600228229401496703205376 : ℚ), (7778305133534290542133024191 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d0 : LeanSuffixReflective.QInterval := ⟨(168155873982150164098533659795 / 1267650600228229401496703205376 : ℚ), (168156620837044608228097064925 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ48_wJ47d2 : LeanSuffixReflective.QInterval := ⟨(-173643551874066978715 / 1267650600228229401496703205376 : ℚ), (-169043715212222957187 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ47 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ46)).widenAll wQ48_wJ47v wQ48_wJ47d0 wQ48_wJ47d1 wQ48_wJ47d2 (by
    norm_num [wJ45, wJ46, wQ48_wJ47v, wQ48_wJ47d0, wQ48_wJ47d1, wQ48_wJ47d2])
private abbrev wQ49_wJ48v : LeanSuffixReflective.QInterval := ⟨(368395774075297465441470736101 / 1267650600228229401496703205376 : ℚ), (46049478173057999790315046795 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d0 : LeanSuffixReflective.QInterval := ⟨(20743436622777999102798008453 / 316912650057057350374175801344 : ℚ), (20743466013191514627870853687 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ49_wJ48d2 : LeanSuffixReflective.QInterval := ⟨(-42833842450963219851 / 633825300114114700748351602688 : ℚ), (-83398408265317108299 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ48 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ43).invPos (by norm_num [wJ43])).widenAll wQ49_wJ48v wQ49_wJ48d0 wQ49_wJ48d1 wQ49_wJ48d2 (by
    norm_num [wJ43, NearOneScalarInterval.Jet3.invPos, wQ49_wJ48v, wQ49_wJ48d0, wQ49_wJ48d1, wQ49_wJ48d2])
private abbrev wQ50_wJ49v : LeanSuffixReflective.QInterval := ⟨(368395773699976738551682029183 / 633825300114114700748351602688 : ℚ), (368395825019085197163139655041 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d0 : LeanSuffixReflective.QInterval := ⟨(20733321324091028886164027911 / 158456325028528675187087900672 : ℚ), (82933942374255370670123905145 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ50_wJ49d2 : LeanSuffixReflective.QInterval := ⟨(-171335369983035947641 / 1267650600228229401496703205376 : ℚ), (-83398408345783425409 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ49 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ45).mul (wJ48)).widenAll wQ50_wJ49v wQ50_wJ49d0 wQ50_wJ49d1 wQ50_wJ49d2 (by
    norm_num [wJ45, wJ48, wQ50_wJ49v, wQ50_wJ49d0, wQ50_wJ49d1, wQ50_wJ49d2])
private abbrev wQ51_wJ50v : LeanSuffixReflective.QInterval := ⟨(92098943516339177845270193175 / 316912650057057350374175801344 : ℚ), (368395825394407059627585887309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d0 : LeanSuffixReflective.QInterval := ⟨(10371650896827395777091410809 / 158456325028528675187087900672 : ℚ), (10371800468094203334703695641 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ51_wJ50d2 : LeanSuffixReflective.QInterval := ⟨(-21416921229496919281 / 316912650057057350374175801344 : ℚ), (-41699204124720063449 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ50 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ44).invPos (by norm_num [wJ44])).widenAll wQ51_wJ50v wQ51_wJ50d0 wQ51_wJ50d1 wQ51_wJ50d2 (by
    norm_num [wJ44, NearOneScalarInterval.Jet3.invPos, wQ51_wJ50v, wQ51_wJ50d0, wQ51_wJ50d1, wQ51_wJ50d2])
private abbrev wQ52_wJ51v : LeanSuffixReflective.QInterval := ⟨(368395773877696912751254615611 / 633825300114114700748351602688 : ℚ), (368395825211718247066038853675 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d0 : LeanSuffixReflective.QInterval := ⟨(165905953339622328737168667891 / 1267650600228229401496703205376 : ℚ), (41477221500291791497021652665 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ52_wJ51d2 : LeanSuffixReflective.QInterval := ⟨(-171335369925567161923 / 1267650600228229401496703205376 : ℚ), (-20849602072418353341 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ51 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((wJ0).mul (wJ0)).mul (wJ0)))).mul (wJ50)).widenAll wQ52_wJ51v wQ52_wJ51d0 wQ52_wJ51d1 wQ52_wJ51d2 (by
    norm_num [wJ35, wJ0, wJ50, wQ52_wJ51v, wQ52_wJ51d0, wQ52_wJ51d1, wQ52_wJ51d2])
private abbrev wQ53_wJ52v : LeanSuffixReflective.QInterval := ⟨(633825300428432966564726063901 / 633825300114114700748351602688 : ℚ), (633825300436985517034434480171 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d0 : LeanSuffixReflective.QInterval := ⟨(34342736899842509031649613 / 633825300114114700748351602688 : ℚ), (4350855613466017977474847 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ53_wJ52d2 : LeanSuffixReflective.QInterval := ⟨(8894582377 / 39614081257132168796771975168 : ℚ), (300326541349 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ52 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ53_wJ52v wQ53_wJ52d0 wQ53_wJ52d1 wQ53_wJ52d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ53_wJ52v, wQ53_wJ52d0, wQ53_wJ52d1, wQ53_wJ52d2])
private abbrev wQ54_wJ53v : LeanSuffixReflective.QInterval := ⟨(39922458152130016423462209 / 1267650600228229401496703205376 : ℚ), (10115489539095642229170465 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d0 : LeanSuffixReflective.QInterval := ⟨(2180998297803359773840784472897 / 1267650600228229401496703205376 : ℚ), (1090499361586288062940971757511 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ54_wJ53d2 : LeanSuffixReflective.QInterval := ⟨(9037696514457877 / 1267650600228229401496703205376 : ℚ), (4704532440922887 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ53 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ0).mul (wJ39)).mul (wJ52)).widenAll wQ54_wJ53v wQ54_wJ53d0 wQ54_wJ53d1 wQ54_wJ53d2 (by
    norm_num [wJ0, wJ39, wJ52, wQ54_wJ53v, wQ54_wJ53d0, wQ54_wJ53d1, wQ54_wJ53d2])
private abbrev wQ55_wJ54v : LeanSuffixReflective.QInterval := ⟨(246869605978805529523 / 1267650600228229401496703205376 : ℚ), (253586874932561128463 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d0 : LeanSuffixReflective.QInterval := ⟨(3371685305505960659998003 / 158456325028528675187087900672 : ℚ), (13668996767658077828492555 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ55_wJ54d2 : LeanSuffixReflective.QInterval := ⟨(-1842803907 / 39614081257132168796771975168 : ℚ), (-13971748357 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev wJ54 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ33).mul (wJ51)).widenAll wQ55_wJ54v wQ55_wJ54d0 wQ55_wJ54d1 wQ55_wJ54d2 (by
    norm_num [wJ33, wJ51, wQ55_wJ54v, wQ55_wJ54d0, wQ55_wJ54d1, wQ55_wJ54d2])
private abbrev wQ56_wJ55v : LeanSuffixReflective.QInterval := ⟨(1267650599797729583551575489597 / 1267650600228229401496703205376 : ℚ), (1267650599824849304831183714377 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d0 : LeanSuffixReflective.QInterval := ⟨(-23205106510696057556308901 / 633825300114114700748351602688 : ℚ), (-44073782500878400625828857 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ56_wJ55d2 : LeanSuffixReflective.QInterval := ⟨(-12513668075 / 79228162514264337593543950336 : ℚ), (-182634433217 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ55 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ53]) (by norm_num [wJ53])).widenAll wQ56_wJ55v wQ56_wJ55d0 wQ56_wJ55d1 wQ56_wJ55d2 (by
    norm_num [wJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ56_wJ55v, wQ56_wJ55d0, wQ56_wJ55d1, wQ56_wJ55d2])
private abbrev wQ57_wJ56v : LeanSuffixReflective.QInterval := ⟨(1267650600228229401479793629207 / 1267650600228229401496703205376 : ℚ), (633825300114114700740639280413 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d0 : LeanSuffixReflective.QInterval := ⟨(-911470445997667 / 316912650057057350374175801344 : ℚ), (-1685328484736487 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ57_wJ56d2 : LeanSuffixReflective.QInterval := ⟨(3 / 633825300114114700748351602688 : ℚ), (1 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ56 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [wJ54]) (by norm_num [wJ54])).widenAll wQ57_wJ56v wQ57_wJ56d0 wQ57_wJ56d1 wQ57_wJ56d2 (by
    norm_num [wJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, wQ57_wJ56v, wQ57_wJ56d0, wQ57_wJ56d1, wQ57_wJ56d2])
private abbrev wQ58_wJ57v : LeanSuffixReflective.QInterval := ⟨(633825300428432966564726063901 / 633825300114114700748351602688 : ℚ), (633825300436985517034434480171 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d0 : LeanSuffixReflective.QInterval := ⟨(34342736899842509031649613 / 633825300114114700748351602688 : ℚ), (4350855613466017977474847 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ58_wJ57d2 : LeanSuffixReflective.QInterval := ⟨(8894582377 / 39614081257132168796771975168 : ℚ), (300326541349 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ57 : NearOneScalarInterval.Jet3 wholeBox :=
  ((wJ35).invPos (by norm_num [wJ35])).widenAll wQ58_wJ57v wQ58_wJ57d0 wQ58_wJ57d1 wQ58_wJ57d2 (by
    norm_num [wJ35, NearOneScalarInterval.Jet3.invPos, wQ58_wJ57v, wQ58_wJ57d0, wQ58_wJ57d1, wQ58_wJ57d2])
private abbrev wQ59_wJ58v : LeanSuffixReflective.QInterval := ⟨(736791548486160558481806163143 / 1267650600228229401496703205376 : ℚ), (92098956396760908036825149785 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d0 : LeanSuffixReflective.QInterval := ⟨(165985798213634759330212812011 / 1267650600228229401496703205376 : ℚ), (165989809876313315427439219473 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ59_wJ58d2 : LeanSuffixReflective.QInterval := ⟨(-171335369760135265773 / 1267650600228229401496703205376 : ℚ), (-83398408202394866823 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev wJ58 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ33).mul (wJ39)).mul (wJ57)).mul (wJ55)).add ((wJ51).mul (wJ56))).widenAll wQ59_wJ58v wQ59_wJ58d0 wQ59_wJ58d1 wQ59_wJ58d2 (by
    norm_num [wJ33, wJ39, wJ57, wJ55, wJ51, wJ56, wQ59_wJ58v, wQ59_wJ58d0, wQ59_wJ58d1, wQ59_wJ58d2])
private abbrev wQ60_wJ59v : LeanSuffixReflective.QInterval := ⟨(316912649976339646343772706947 / 316912650057057350374175801344 : ℚ), (633825299956955567918100652125 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d0 : LeanSuffixReflective.QInterval := ⟨(-4350855609033363420654971 / 158456325028528675187087900672 : ℚ), (-34342736865780916678761807 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev wQ60_wJ59d2 : LeanSuffixReflective.QInterval := ⟨(-75081635261 / 633825300114114700748351602688 : ℚ), (-142313317891 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ59 : NearOneScalarInterval.Jet3 wholeBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((wJ5).mul (wJ4)).neg)).widenAll wQ60_wJ59v wQ60_wJ59d0 wQ60_wJ59d1 wQ60_wJ59d2 (by
    norm_num [wJ5, wJ4, wQ60_wJ59v, wQ60_wJ59d0, wQ60_wJ59d1, wQ60_wJ59d2])
private abbrev wQ61_wJ60v : LeanSuffixReflective.QInterval := ⟨(-998372537233800236603201 / 1267650600228229401496703205376 : ℚ), (499186685744616548717597 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d0 : LeanSuffixReflective.QInterval := ⟨(-138061599282863366897451 / 79228162514264337593543950336 : ℚ), (2208987534500499475421215 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d1 : LeanSuffixReflective.QInterval := ⟨(-2778241616906969449081 / 1267650600228229401496703205376 : ℚ), (-676160236752743285557 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev wQ61_wJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev wJ60 : NearOneScalarInterval.Jet3 wholeBox :=
  (((wJ8).mul (wJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((wJ5).mul (wJ31))).neg)).widenAll wQ61_wJ60v wQ61_wJ60d0 wQ61_wJ60d1 wQ61_wJ60d2 (by
    norm_num [wJ8, wJ20, wJ5, wJ31, wQ61_wJ60v, wQ61_wJ60d0, wQ61_wJ60d1, wQ61_wJ60d2])
private abbrev wQ62_wJ61v : LeanSuffixReflective.QInterval := ⟨(-2257707302537946950105387 / 1267650600228229401496703205376 : ℚ), (2257706844641976414805063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d0 : LeanSuffixReflective.QInterval := ⟨(-5603983953974414241568445 / 633825300114114700748351602688 : ℚ), (11207967923703844835999813 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d1 : LeanSuffixReflective.QInterval := ⟨(-72616156078824583217 / 1267650600228229401496703205376 : ℚ), (36308096244360398235 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ62_wJ61d2 : LeanSuffixReflective.QInterval := ⟨(1983374914956025896677 / 1267650600228229401496703205376 : ℚ), (2074143946154665650583 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev wJ61 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((wJ4).add ((wJ3).neg))).mul ((wJ8).add (wJ59))).add (((wJ8).mul (wJ8)).mul ((wJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (wJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (wJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((wJ59).mul (wJ59))).mul ((wJ31).add ((wJ8).mul (wJ22)))).neg)).widenAll wQ62_wJ61v wQ62_wJ61d0 wQ62_wJ61d1 wQ62_wJ61d2 (by
    norm_num [wJ4, wJ3, wJ8, wJ59, wJ58, wJ49, wJ31, wJ22, wQ62_wJ61v, wQ62_wJ61d0, wQ62_wJ61d1, wQ62_wJ61d2])
private abbrev wQ63_wJ62v : LeanSuffixReflective.QInterval := ⟨(-933954078852408104180055 / 1267650600228229401496703205376 : ℚ), (933675848723691264748137 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d0 : LeanSuffixReflective.QInterval := ⟨(-17324911431909846625764821 / 1267650600228229401496703205376 : ℚ), (-1602456572462484953586989 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d1 : LeanSuffixReflective.QInterval := ⟨(982608245115057978085 / 1267650600228229401496703205376 : ℚ), (1046151240257361082351 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev wQ63_wJ62d2 : LeanSuffixReflective.QInterval := ⟨(-32408520645770499991 / 79228162514264337593543950336 : ℚ), (-61980424303747020245 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev wJ62 : NearOneScalarInterval.Jet3 wholeBox :=
  (((((wJ3).add ((wJ4).neg)).mul (wJ20)).add ((wJ59).mul (wJ22))).add (((wJ8).mul (wJ49)).neg)).widenAll wQ63_wJ62v wQ63_wJ62d0 wQ63_wJ62d1 wQ63_wJ62d2 (by
    norm_num [wJ3, wJ4, wJ20, wJ59, wJ22, wJ8, wJ49, wQ63_wJ62v, wQ63_wJ62d0, wQ63_wJ62d1, wQ63_wJ62d2])
private abbrev wQ64_wJ63v : LeanSuffixReflective.QInterval := ⟨(469052037004504744133380411433 / 1267650600228229401496703205376 : ℚ), (234526188351754198177357113545 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d0 : LeanSuffixReflective.QInterval := ⟨(-26408179825148302767405743477 / 316912650057057350374175801344 : ℚ), (-3301019248510468997180752499 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d1 : LeanSuffixReflective.QInterval := ⟨(-109074103253449679837 / 316912650057057350374175801344 : ℚ), (-212369702903427714413 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev wQ64_wJ63d2 : LeanSuffixReflective.QInterval := ⟨(212369702903427714413 / 633825300114114700748351602688 : ℚ), (109074103253449679837 / 316912650057057350374175801344 : ℚ), by norm_num⟩
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
private abbrev cQ4_cJ3v : LeanSuffixReflective.QInterval := ⟨(469042473143554163352828454879 / 1267650600228229401496703205376 : ℚ), (14657577285736067604775889215 / 39614081257132168796771975168 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d0 : LeanSuffixReflective.QInterval := ⟨(-633830271245322315788439906001 / 1267650600228229401496703205376 : ℚ), (-39614391952832644736777494125 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d1 : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ4_cJ3d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ3 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (491838928142993121175353635602441465 / 1329227995784915872903807060280344576 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-664619210501335092600179162874332053 / 1329227995784915872903807060280344576 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ1))).widenAll cQ4_cJ3v cQ4_cJ3d0 cQ4_cJ3d1 cQ4_cJ3d2 (by
    norm_num [cJ0, cJ1, cQ4_cJ3v, cQ4_cJ3d0, cQ4_cJ3d1, cQ4_cJ3d2])
private abbrev cQ5_cJ4v : LeanSuffixReflective.QInterval := ⟨(234523669999390183399218943535 / 316912650057057350374175801344 : ℚ), (938094679997560733596875774141 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d0 : LeanSuffixReflective.QInterval := ⟨(-739462938871786425278143432939 / 1267650600228229401496703205376 : ℚ), (-369731469435893212639071716469 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ5_cJ4d2 : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ4 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (491838928095393980932283885614535351 / 664613997892457936451903530140172288 : ℚ)).add ((NearOneScalarInterval.Jet3.rational (-387691545295211161336227264168697623 / 664613997892457936451903530140172288 : ℚ)).mul (cJ0))).add (((cJ0).mul (cJ0)).mul (cJ2))).widenAll cQ5_cJ4v cQ5_cJ4d0 cQ5_cJ4d1 cQ5_cJ4d2 (by
    norm_num [cJ0, cJ2, cQ5_cJ4v, cQ5_cJ4d0, cQ5_cJ4d1, cQ5_cJ4d2])
private abbrev cQ6_cJ5v : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d0 : LeanSuffixReflective.QInterval := ⟨(23360687175711578635676161 / 633825300114114700748351602688 : ℚ), (46721374351423157271352323 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ6_cJ5d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ5 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ6_cJ5v cQ6_cJ5d0 cQ6_cJ5d1 cQ6_cJ5d2 (by
    norm_num [cJ0, cQ6_cJ5v, cQ6_cJ5d0, cQ6_cJ5d1, cQ6_cJ5d2])
private abbrev cQ7_cJ6v : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d0 : LeanSuffixReflective.QInterval := ⟨(23360687175711578635676161 / 633825300114114700748351602688 : ℚ), (46721374351423157271352323 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ7_cJ6d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ6 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ7_cJ6v cQ7_cJ6d0 cQ7_cJ6d1 cQ7_cJ6d2 (by
    norm_num [cJ0, cQ7_cJ6v, cQ7_cJ6d0, cQ7_cJ6d1, cQ7_cJ6d2])
private abbrev cQ8_cJ7v : LeanSuffixReflective.QInterval := ⟨(43387515765979304860252528089 / 316912650057057350374175801344 : ℚ), (86775031531958609720505056179 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d0 : LeanSuffixReflective.QInterval := ⟨(-469046151872812085156088811141 / 1267650600228229401496703205376 : ℚ), (-234523075936406042578044405569 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d1 : LeanSuffixReflective.QInterval := ⟨(318576885059843877615 / 1267650600228229401496703205376 : ℚ), (19911055316240242351 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ8_cJ7d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ7 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ3).mul (cJ3)).widenAll cQ8_cJ7v cQ8_cJ7d0 cQ8_cJ7d1 cQ8_cJ7d2 (by
    norm_num [cJ3, cQ8_cJ7v, cQ8_cJ7d0, cQ8_cJ7d1, cQ8_cJ7d2])
private abbrev cQ9_cJ8v : LeanSuffixReflective.QInterval := ⟨(158456325008617619870847658321 / 158456325028528675187087900672 : ℚ), (1267650600068940958966781266569 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d0 : LeanSuffixReflective.QInterval := ⟨(-17287126363935914762671125 / 1267650600228229401496703205376 : ℚ), (-17287126363935914762671123 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d1 : LeanSuffixReflective.QInterval := ⟨(-146198782505 / 1267650600228229401496703205376 : ℚ), (-18274847813 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ9_cJ8d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ8 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ6).mul (cJ3)).neg)).widenAll cQ9_cJ8v cQ9_cJ8d0 cQ9_cJ8d1 cQ9_cJ8d2 (by
    norm_num [cJ6, cJ3, cQ9_cJ8v, cQ9_cJ8d0, cQ9_cJ8d1, cQ9_cJ8d2])
private abbrev cQ10_cJ9v : LeanSuffixReflective.QInterval := ⟨(938084946228170126373508562581 / 1267650600228229401496703205376 : ℚ), (117260618278521265796688570323 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d0 : LeanSuffixReflective.QInterval := ⟨(-633833469404002629226451686767 / 633825300114114700748351602688 : ℚ), (-633833469404002629226451686765 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d1 : LeanSuffixReflective.QInterval := ⟨(860997036809085334277 / 1267650600228229401496703205376 : ℚ), (107624629601135666785 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ10_cJ9d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ9 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add (((cJ6).mul (cJ7)).neg)).widenAll cQ10_cJ9v cQ10_cJ9d0 cQ10_cJ9d1 cQ10_cJ9d2 (by
    norm_num [cJ3, cJ6, cJ7, cQ10_cJ9v, cQ10_cJ9d0, cQ10_cJ9d1, cQ10_cJ9d2])
private abbrev cQ11_cJ10v : LeanSuffixReflective.QInterval := ⟨(14658307306289399213702792147 / 19807040628566084398385987584 : ℚ), (938131667602521549676978697411 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d0 : LeanSuffixReflective.QInterval := ⟨(1267634261648485278020430420681 / 1267650600228229401496703205376 : ℚ), (1267634261648485278020430420685 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d1 : LeanSuffixReflective.QInterval := ⟨(860997036809085334277 / 1267650600228229401496703205376 : ℚ), (107624629601135666785 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ11_cJ10d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ10 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ3)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ6).mul (cJ7)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ11_cJ10v cQ11_cJ10d0 cQ11_cJ10d1 cQ11_cJ10d2 (by
    norm_num [cJ3, cJ0, cJ6, cJ7, cQ11_cJ10v, cQ11_cJ10d0, cQ11_cJ10d1, cQ11_cJ10d2])
private abbrev cQ11_root11 : LeanSuffixReflective.QInterval := ⟨(1090487939021430059314813285153 / 1267650600228229401496703205376 : ℚ), (272621984755357514828703321289 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11v : LeanSuffixReflective.QInterval := ⟨(1090487939021430059314813285153 / 1267650600228229401496703205376 : ℚ), (272621984755357514828703321289 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d0 : LeanSuffixReflective.QInterval := ⟨(-368403605937972316471929262915 / 633825300114114700748351602688 : ℚ), (-736807211875944632943858525825 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d1 : LeanSuffixReflective.QInterval := ⟨(500438093558921568133 / 1267650600228229401496703205376 : ℚ), (500438093558921568135 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ12_cJ11d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ11 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ9).sqrt cQ11_root11 (by norm_num [cQ11_root11]) (by norm_num [cJ9, cQ11_root11]) (by norm_num [cJ9, cQ11_root11])).widenAll cQ12_cJ11v cQ12_cJ11d0 cQ12_cJ11d1 cQ12_cJ11d2 (by
    norm_num [cJ9, cQ11_root11, NearOneScalarInterval.Jet3.sqrt, cQ12_cJ11v, cQ12_cJ11d0, cQ12_cJ11d1, cQ12_cJ11d2])
private abbrev cQ12_root12 : LeanSuffixReflective.QInterval := ⟨(1090515094590371194181032266745 / 1267650600228229401496703205376 : ℚ), (1090515094590371194181032266747 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12v : LeanSuffixReflective.QInterval := ⟨(1090515094590371194181032266745 / 1267650600228229401496703205376 : ℚ), (1090515094590371194181032266747 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d0 : LeanSuffixReflective.QInterval := ⟨(736769871696354228842315024689 / 1267650600228229401496703205376 : ℚ), (368384935848177114421157512347 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d1 : LeanSuffixReflective.QInterval := ⟨(500425631850488715977 / 1267650600228229401496703205376 : ℚ), (125106407962622178995 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ13_cJ12d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ12 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ10).sqrt cQ12_root12 (by norm_num [cQ12_root12]) (by norm_num [cJ10, cQ12_root12]) (by norm_num [cJ10, cQ12_root12])).widenAll cQ13_cJ12v cQ13_cJ12d0 cQ13_cJ12d1 cQ13_cJ12d2 (by
    norm_num [cJ10, cQ12_root12, NearOneScalarInterval.Jet3.sqrt, cQ13_cJ12v, cQ13_cJ12d0, cQ13_cJ12d1, cQ13_cJ12d2])
private abbrev cQ14_cJ13v : LeanSuffixReflective.QInterval := ⟨(1267650600228237334866685051241 / 1267650600228229401496703205376 : ℚ), (633825300114118667433342525621 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d0 : LeanSuffixReflective.QInterval := ⟨(1291495555375912715765 / 1267650600228229401496703205376 : ℚ), (645747777687956357883 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ14_cJ13d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ13 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ14_cJ13v cQ14_cJ13d0 cQ14_cJ13d1 cQ14_cJ13d2 (by
    norm_num [cJ0, cQ14_cJ13v, cQ14_cJ13d0, cQ14_cJ13d1, cQ14_cJ13d2])
private abbrev cQ15_cJ14v : LeanSuffixReflective.QInterval := ⟨(545250758402952019531060086937 / 316912650057057350374175801344 : ℚ), (2181003033611808078124240347755 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d0 : LeanSuffixReflective.QInterval := ⟨(-18669534297306645114527103 / 633825300114114700748351602688 : ℚ), (-37339068594613290229054193 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d1 : LeanSuffixReflective.QInterval := ⟨(500431862704706708007 / 633825300114114700748351602688 : ℚ), (250215931352353354005 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ15_cJ14d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ14 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ12).add ((cJ13).mul (cJ11))).widenAll cQ15_cJ14v cQ15_cJ14d0 cQ15_cJ14d1 cQ15_cJ14d2 (by
    norm_num [cJ12, cJ13, cJ11, cQ15_cJ14v, cQ15_cJ14d0, cQ15_cJ14d1, cQ15_cJ14d2])
private abbrev cQ16_cJ15v : LeanSuffixReflective.QInterval := ⟨(403505718025942275041854549277 / 316912650057057350374175801344 : ℚ), (807011436051884550083709098561 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d0 : LeanSuffixReflective.QInterval := ⟨(-110054086641711707711861521 / 1267650600228229401496703205376 : ℚ), (-55027043320855853855930745 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d1 : LeanSuffixReflective.QInterval := ⟨(1111014235268056104909 / 633825300114114700748351602688 : ℚ), (2222028470536112209831 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ16_cJ15d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ15 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).mul (cJ12)).mul (cJ14)).widenAll cQ16_cJ15v cQ16_cJ15d0 cQ16_cJ15d1 cQ16_cJ15d2 (by
    norm_num [cJ11, cJ12, cJ14, cQ16_cJ15v, cQ16_cJ15d0, cQ16_cJ15d1, cQ16_cJ15d2])
private abbrev cQ17_cJ16v : LeanSuffixReflective.QInterval := ⟨(1090501516805910863775489163517 / 633825300114114700748351602688 : ℚ), (545250758402955431887744581761 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d0 : LeanSuffixReflective.QInterval := ⟨(-9334211641535791970438585 / 316912650057057350374175801344 : ℚ), (-9334211641535791970438581 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d1 : LeanSuffixReflective.QInterval := ⟨(488702990922568203 / 618970019642690137449562112 : ℚ), (1000863725409419679751 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ17_cJ16d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ16 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ13).mul (cJ14)).widenAll cQ17_cJ16v cQ17_cJ16d0 cQ17_cJ16d1 cQ17_cJ16d2 (by
    norm_num [cJ13, cJ14, cQ17_cJ16v, cQ17_cJ16d0, cQ17_cJ16d1, cQ17_cJ16d2])
private abbrev cQ18_cJ17v : LeanSuffixReflective.QInterval := ⟨(272625379201476862844079392955 / 158456325028528675187087900672 : ℚ), (2181003033611814902752635143651 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d0 : LeanSuffixReflective.QInterval := ⟨(-2333622349926404931293831 / 79228162514264337593543950336 : ℚ), (-37337957598822478900701277 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d1 : LeanSuffixReflective.QInterval := ⟨(500431862704708273959 / 633825300114114700748351602688 : ℚ), (125107965676177068491 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ18_cJ17d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ17 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ11).add (cJ12)).mul (((cJ8).mul (cJ8)).add ((cJ6).mul ((cJ11).mul (cJ12))))).widenAll cQ18_cJ17v cQ18_cJ17d0 cQ18_cJ17d1 cQ18_cJ17d2 (by
    norm_num [cJ11, cJ12, cJ8, cJ6, cQ18_cJ17v, cQ18_cJ17d0, cQ18_cJ17d1, cQ18_cJ17d2])
private abbrev cQ19_cJ18v : LeanSuffixReflective.QInterval := ⟨(2535301199819312966283729740081 / 1267650600228229401496703205376 : ℚ), (1267650599909656483141864870043 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d0 : LeanSuffixReflective.QInterval := ⟨(-69147213951499870097053131 / 1267650600228229401496703205376 : ℚ), (-34573606975749935048526561 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d1 : LeanSuffixReflective.QInterval := ⟨(-584795129947 / 1267650600228229401496703205376 : ℚ), (-292397564971 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ19_cJ18d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ18 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ8)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ19_cJ18v cQ19_cJ18d0 cQ19_cJ18d1 cQ19_cJ18d2 (by
    norm_num [cJ8, cJ0, cQ19_cJ18v, cQ19_cJ18d0, cQ19_cJ18d1, cQ19_cJ18d2])
private abbrev cQ20_cJ19v : LeanSuffixReflective.QInterval := ⟨(995610453874458276342278956747 / 1267650600228229401496703205376 : ℚ), (248902613468614569085569739189 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d0 : LeanSuffixReflective.QInterval := ⟨(67886893702612280606432331 / 1267650600228229401496703205376 : ℚ), (67886893702612280606432351 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d1 : LeanSuffixReflective.QInterval := ⟨(-342664718745416108689 / 316912650057057350374175801344 : ℚ), (-1370658874981664434747 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ20_cJ19d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ19 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ15).invPos (by norm_num [cJ15])).widenAll cQ20_cJ19v cQ20_cJ19d0 cQ20_cJ19d1 cQ20_cJ19d2 (by
    norm_num [cJ15, NearOneScalarInterval.Jet3.invPos, cQ20_cJ19v, cQ20_cJ19d0, cQ20_cJ19d1, cQ20_cJ19d2])
private abbrev cQ21_cJ20v : LeanSuffixReflective.QInterval := ⟨(1991220907248503382402041838983 / 1267650600228229401496703205376 : ℚ), (1991220907248503382402041839005 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d0 : LeanSuffixReflective.QInterval := ⟨(81465692495423542766023455 / 1267650600228229401496703205376 : ℚ), (81465692495423542766023503 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d1 : LeanSuffixReflective.QInterval := ⟨(-2741317749733706092589 / 1267650600228229401496703205376 : ℚ), (-1370658874866853046283 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ21_cJ20d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ20 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ19)).widenAll cQ21_cJ20v cQ21_cJ20d0 cQ21_cJ20d1 cQ21_cJ20d2 (by
    norm_num [cJ18, cJ19, cQ21_cJ20v, cQ21_cJ20d0, cQ21_cJ20d1, cQ21_cJ20d2])
private abbrev cQ22_cJ21v : LeanSuffixReflective.QInterval := ⟨(368394270776836429371629439339 / 633825300114114700748351602688 : ℚ), (368394270776836429371629439341 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d0 : LeanSuffixReflective.QInterval := ⟨(6306584700646968825755399 / 633825300114114700748351602688 : ℚ), (12613169401293937651510805 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d1 : LeanSuffixReflective.QInterval := ⟨(-169056372956340888603 / 633825300114114700748351602688 : ℚ), (-338112745912681777203 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ22_cJ21d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ21 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ16).invPos (by norm_num [cJ16])).widenAll cQ22_cJ21v cQ22_cJ21d0 cQ22_cJ21d1 cQ22_cJ21d2 (by
    norm_num [cJ16, NearOneScalarInterval.Jet3.invPos, cQ22_cJ21v, cQ22_cJ21d0, cQ22_cJ21d1, cQ22_cJ21d2])
private abbrev cQ23_cJ22v : LeanSuffixReflective.QInterval := ⟨(368394270684255368055956494689 / 316912650057057350374175801344 : ℚ), (92098567671063842013989123673 / 79228162514264337593543950336 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d0 : LeanSuffixReflective.QInterval := ⟨(-14963659071186853225501113 / 1267650600228229401496703205376 : ℚ), (-14963659071186853225501093 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d1 : LeanSuffixReflective.QInterval := ⟨(-676225491995318289941 / 1267650600228229401496703205376 : ℚ), (-676225491995318289931 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ23_cJ22d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ22 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ18).mul (cJ21)).widenAll cQ23_cJ22v cQ23_cJ22d0 cQ23_cJ22d1 cQ23_cJ22d2 (by
    norm_num [cJ18, cJ21, cQ23_cJ22v, cQ23_cJ22d0, cQ23_cJ22d1, cQ23_cJ22d2])
private abbrev cQ24_cJ23v : LeanSuffixReflective.QInterval := ⟨(736788541553675164303196291859 / 1267650600228229401496703205376 : ℚ), (92098567694209395537899536483 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d0 : LeanSuffixReflective.QInterval := ⟨(3153386182855462208830399 / 316912650057057350374175801344 : ℚ), (12613544731421848835321603 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d1 : LeanSuffixReflective.QInterval := ⟨(-42264093239085354407 / 158456325028528675187087900672 : ℚ), (-84528186478170708813 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ24_cJ23d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ23 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ17).invPos (by norm_num [cJ17])).widenAll cQ24_cJ23v cQ24_cJ23d0 cQ24_cJ23d1 cQ24_cJ23d2 (by
    norm_num [cJ17, NearOneScalarInterval.Jet3.invPos, cQ24_cJ23v, cQ24_cJ23d0, cQ24_cJ23d1, cQ24_cJ23d2])
private abbrev cQ25_cJ24v : LeanSuffixReflective.QInterval := ⟨(1473577082922190511494643914343 / 1267650600228229401496703205376 : ℚ), (1473577082922190511494643914355 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d0 : LeanSuffixReflective.QInterval := ⟨(5132465847328120286038021 / 1267650600228229401496703205376 : ℚ), (5132465847328120286038039 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d1 : LeanSuffixReflective.QInterval := ⟨(-676225491910344096303 / 1267650600228229401496703205376 : ℚ), (-169056372977586024073 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ25_cJ24d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ24 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ23)).widenAll cQ25_cJ24v cQ25_cJ24d0 cQ25_cJ24d1 cQ25_cJ24d2 (by
    norm_num [cJ8, cJ0, cJ23, cQ25_cJ24v, cQ25_cJ24d0, cQ25_cJ24d1, cQ25_cJ24d2])
private abbrev cQ26_cJ25v : LeanSuffixReflective.QInterval := ⟨(316912650096879461011660190103 / 316912650057057350374175801344 : ℚ), (633825300193758922023320380207 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d0 : LeanSuffixReflective.QInterval := ⟨(8643563184140195878562285 / 633825300114114700748351602688 : ℚ), (17287126368280391757124573 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d1 : LeanSuffixReflective.QInterval := ⟨(36549695635 / 316912650057057350374175801344 : ℚ), (73099391271 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ26_cJ25d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ25 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ26_cJ25v cQ26_cJ25d0 cQ26_cJ25d1 cQ26_cJ25d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ26_cJ25v, cQ26_cJ25d0, cQ26_cJ25d1, cQ26_cJ25d2])
private abbrev cQ27_cJ26v : LeanSuffixReflective.QInterval := ⟨(20096375123974792505745795 / 1267650600228229401496703205376 : ℚ), (5024093780993698126436449 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d0 : LeanSuffixReflective.QInterval := ⟨(1090528672441876395074090541277 / 1267650600228229401496703205376 : ℚ), (545264336220938197537045270641 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d1 : LeanSuffixReflective.QInterval := ⟨(9222010104889601 / 1267650600228229401496703205376 : ℚ), (4611005052444801 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ27_cJ26d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ26 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ12)).mul (cJ25)).widenAll cQ27_cJ26v cQ27_cJ26d0 cQ27_cJ26d1 cQ27_cJ26d2 (by
    norm_num [cJ0, cJ12, cJ25, cQ27_cJ26v, cQ27_cJ26d0, cQ27_cJ26d1, cQ27_cJ26d2])
private abbrev cQ28_cJ27v : LeanSuffixReflective.QInterval := ⟨(500431862627123495515 / 1267650600228229401496703205376 : ℚ), (500431862627123495517 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d0 : LeanSuffixReflective.QInterval := ⟨(54311137877187852237057195 / 1267650600228229401496703205376 : ℚ), (54311137877187852237057197 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d1 : LeanSuffixReflective.QInterval := ⟨(-114824255343 / 633825300114114700748351602688 : ℚ), (-229648510685 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ28_cJ27d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ27 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ6).mul (cJ24)).widenAll cQ28_cJ27v cQ28_cJ27d0 cQ28_cJ27d1 cQ28_cJ27d2 (by
    norm_num [cJ6, cJ24, cQ28_cJ27v, cQ28_cJ27d0, cQ28_cJ27d1, cQ28_cJ27d2])
private abbrev cQ29_cJ28v : LeanSuffixReflective.QInterval := ⟨(1267650600122031817543417070175 / 1267650600228229401496703205376 : ℚ), (633825300063007113470832650123 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d0 : LeanSuffixReflective.QInterval := ⟨(-11525639318424206839365655 / 1267650600228229401496703205376 : ℚ), (-11093374056270308978470309 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d1 : LeanSuffixReflective.QInterval := ⟨(-97466086813 / 1267650600228229401496703205376 : ℚ), (-93810653703 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ29_cJ28d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ28 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ26).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ26]) (by norm_num [cJ26])).widenAll cQ29_cJ28v cQ29_cJ28d0 cQ29_cJ28d1 cQ29_cJ28d2 (by
    norm_num [cJ26, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ29_cJ28v, cQ29_cJ28d0, cQ29_cJ28d1, cQ29_cJ28d2])
private abbrev cQ30_cJ29v : LeanSuffixReflective.QInterval := ⟨(1267650600228229401430851187717 / 1267650600228229401496703205376 : ℚ), (316912650057057350358330159595 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d0 : LeanSuffixReflective.QInterval := ⟨(-14293646259726833 / 1267650600228229401496703205376 : ℚ), (-13757634523326001 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d1 : LeanSuffixReflective.QInterval := ⟨(29 / 633825300114114700748351602688 : ℚ), (61 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ30_cJ29d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ29 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ27).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ27]) (by norm_num [cJ27])).widenAll cQ30_cJ29v cQ30_cJ29d0 cQ30_cJ29d1 cQ30_cJ29d2 (by
    norm_num [cJ27, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ30_cJ29v, cQ30_cJ29d0, cQ30_cJ29d1, cQ30_cJ29d2])
private abbrev cQ31_cJ30v : LeanSuffixReflective.QInterval := ⟨(316912650096879461011660190103 / 316912650057057350374175801344 : ℚ), (633825300193758922023320380207 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d0 : LeanSuffixReflective.QInterval := ⟨(8643563184140195878562285 / 633825300114114700748351602688 : ℚ), (17287126368280391757124573 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d1 : LeanSuffixReflective.QInterval := ⟨(36549695635 / 316912650057057350374175801344 : ℚ), (73099391271 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ31_cJ30d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ30 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ8).invPos (by norm_num [cJ8])).widenAll cQ31_cJ30v cQ31_cJ30d0 cQ31_cJ30d1 cQ31_cJ30d2 (by
    norm_num [cJ8, NearOneScalarInterval.Jet3.invPos, cQ31_cJ30v, cQ31_cJ30d0, cQ31_cJ30d1, cQ31_cJ30d2])
private abbrev cQ32_cJ31v : LeanSuffixReflective.QInterval := ⟨(1473577083292533200888737608779 / 1267650600228229401496703205376 : ℚ), (1473577083292533200892771671579 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d0 : LeanSuffixReflective.QInterval := ⟨(5665683285821145115839725 / 158456325028528675187087900672 : ℚ), (45325466287444801164888071 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d1 : LeanSuffixReflective.QInterval := ⟨(-169056372935099456163 / 316912650057057350374175801344 : ℚ), (-676225491740397824633 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ32_cJ31d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ31 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ6).mul (cJ12)).mul (cJ30)).mul (cJ28)).add ((cJ24).mul (cJ29))).widenAll cQ32_cJ31v cQ32_cJ31d0 cQ32_cJ31d1 cQ32_cJ31d2 (by
    norm_num [cJ6, cJ12, cJ30, cJ28, cJ24, cJ29, cQ32_cJ31v, cQ32_cJ31d0, cQ32_cJ31d1, cQ32_cJ31d2])
private abbrev cQ33_cJ32v : LeanSuffixReflective.QInterval := ⟨(234523669999390183399218943535 / 158456325028528675187087900672 : ℚ), (938094679997560733596875774141 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d0 : LeanSuffixReflective.QInterval := ⟨(-739462938871786425278143432939 / 633825300114114700748351602688 : ℚ), (-369731469435893212639071716469 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ33_cJ32d2 : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 633825300114114700748351602688 : ℚ), (215249259229318785961 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ32 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ4)).widenAll cQ33_cJ32v cQ33_cJ32d0 cQ33_cJ32d1 cQ33_cJ32d2 (by
    norm_num [cJ4, cQ33_cJ32v, cQ33_cJ32d0, cQ33_cJ32d1, cQ33_cJ32d2])
private abbrev cQ34_cJ33v : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d0 : LeanSuffixReflective.QInterval := ⟨(23360687175711578635676161 / 633825300114114700748351602688 : ℚ), (46721374351423157271352323 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ34_cJ33d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ33 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ0).mul (cJ0)).widenAll cQ34_cJ33v cQ34_cJ33d0 cQ34_cJ33d1 cQ34_cJ33d2 (by
    norm_num [cJ0, cQ34_cJ33v, cQ34_cJ33d0, cQ34_cJ33d1, cQ34_cJ33d2])
private abbrev cQ35_cJ34v : LeanSuffixReflective.QInterval := ⟨(1388429317165606482243084124197 / 633825300114114700748351602688 : ℚ), (2776858634331212964486168248401 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d0 : LeanSuffixReflective.QInterval := ⟨(-4377775698673386244424882317271 / 1267650600228229401496703205376 : ℚ), (-4377775698673386244424882317259 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ35_cJ34d2 : LeanSuffixReflective.QInterval := ⟨(1274320762646016937005 / 633825300114114700748351602688 : ℚ), (2548641525292033874017 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ34 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ32).mul (cJ32)).widenAll cQ35_cJ34v cQ35_cJ34d0 cQ35_cJ34d1 cQ35_cJ34d2 (by
    norm_num [cJ32, cQ35_cJ34v, cQ35_cJ34d0, cQ35_cJ34d1, cQ35_cJ34d2])
private abbrev cQ36_cJ35v : LeanSuffixReflective.QInterval := ⟨(1267650599591069020173694736871 / 1267650600228229401496703205376 : ℚ), (633825299795534510086847368437 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d0 : LeanSuffixReflective.QInterval := ⟨(-69149581715425252333460611 / 1267650600228229401496703205376 : ℚ), (-69149581715425252333460607 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ36_cJ35d2 : LeanSuffixReflective.QInterval := ⟨(-146198782505 / 633825300114114700748351602688 : ℚ), (-292397565009 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ35 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ33).mul (cJ32)).neg)).widenAll cQ36_cJ35v cQ36_cJ35d0 cQ36_cJ35d1 cQ36_cJ35d2 (by
    norm_num [cJ33, cJ32, cQ36_cJ35v, cQ36_cJ35d0, cQ36_cJ35d1, cQ36_cJ35d2])
private abbrev cQ37_cJ36v : LeanSuffixReflective.QInterval := ⟨(3752378719047212159319487150693 / 1267650600228229401496703205376 : ℚ), (938094679761803039829871787675 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d0 : LeanSuffixReflective.QInterval := ⟨(-1478977049875359898137149605093 / 633825300114114700748351602688 : ℚ), (-46218032808604996816785925159 / 19807040628566084398385987584 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ37_cJ36d2 : LeanSuffixReflective.QInterval := ⟨(1721994072969022830415 / 1267650600228229401496703205376 : ℚ), (430498518242255707605 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ36 : NearOneScalarInterval.Jet3 centerBox :=
  (((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add (((cJ33).mul (cJ34)).neg)).widenAll cQ37_cJ36v cQ37_cJ36d0 cQ37_cJ36d1 cQ37_cJ36d2 (by
    norm_num [cJ32, cJ33, cJ34, cQ37_cJ36v, cQ37_cJ36d0, cQ37_cJ36d1, cQ37_cJ36d2])
private abbrev cQ38_cJ37v : LeanSuffixReflective.QInterval := ⟨(234526590026347723913934830345 / 79228162514264337593543950336 : ℚ), (469053180052695447827869660691 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d0 : LeanSuffixReflective.QInterval := ⟨(-422652899294229259800965415971 / 1267650600228229401496703205376 : ℚ), (-422652899294229259800965415961 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ38_cJ37d2 : LeanSuffixReflective.QInterval := ⟨(1721994072969022830415 / 1267650600228229401496703205376 : ℚ), (430498518242255707605 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ37 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ32)).add ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ0))).add (((cJ33).mul (cJ34)).neg)).add (((cJ0).mul (cJ0)).mul ((cJ0).mul (cJ0)))).widenAll cQ38_cJ37v cQ38_cJ37d0 cQ38_cJ37d1 cQ38_cJ37d2 (by
    norm_num [cJ32, cJ0, cJ33, cJ34, cQ38_cJ37v, cQ38_cJ37d0, cQ38_cJ37d1, cQ38_cJ37d2])
private abbrev cQ38_root38 : LeanSuffixReflective.QInterval := ⟨(1090493596437392321761111282709 / 633825300114114700748351602688 : ℚ), (2180987192874784643522222565421 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38v : LeanSuffixReflective.QInterval := ⟨(1090493596437392321761111282709 / 633825300114114700748351602688 : ℚ), (2180987192874784643522222565421 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d0 : LeanSuffixReflective.QInterval := ⟨(-429811360452567754359216738877 / 633825300114114700748351602688 : ℚ), (-859622720905135508718433477749 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ39_cJ38d2 : LeanSuffixReflective.QInterval := ⟨(500435497127185484435 / 1267650600228229401496703205376 : ℚ), (500435497127185484437 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ38 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ36).sqrt cQ38_root38 (by norm_num [cQ38_root38]) (by norm_num [cJ36, cQ38_root38]) (by norm_num [cJ36, cQ38_root38])).widenAll cQ39_cJ38v cQ39_cJ38d0 cQ39_cJ38d1 cQ39_cJ38d2 (by
    norm_num [cJ36, cQ38_root38, NearOneScalarInterval.Jet3.sqrt, cQ39_cJ38v, cQ39_cJ38d0, cQ39_cJ38d1, cQ39_cJ38d2])
private abbrev cQ39_root39 : LeanSuffixReflective.QInterval := ⟨(136312548169725457621664204033 / 79228162514264337593543950336 : ℚ), (2181000770715607321946627264531 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39v : LeanSuffixReflective.QInterval := ⟨(136312548169725457621664204033 / 79228162514264337593543950336 : ℚ), (2181000770715607321946627264531 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d0 : LeanSuffixReflective.QInterval := ⟨(-122828063307547065442853766251 / 1267650600228229401496703205376 : ℚ), (-122828063307547065442853766247 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ40_cJ39d2 : LeanSuffixReflective.QInterval := ⟨(250216190830644353249 / 633825300114114700748351602688 : ℚ), (500432381661288706501 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ39 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ37).sqrt cQ39_root39 (by norm_num [cQ39_root39]) (by norm_num [cJ37, cQ39_root39]) (by norm_num [cJ37, cQ39_root39])).widenAll cQ40_cJ39v cQ40_cJ39d0 cQ40_cJ39d1 cQ40_cJ39d2 (by
    norm_num [cJ37, cQ39_root39, NearOneScalarInterval.Jet3.sqrt, cQ40_cJ39v, cQ40_cJ39d0, cQ40_cJ39d1, cQ40_cJ39d2])
private abbrev cQ41_cJ40v : LeanSuffixReflective.QInterval := ⟨(1267650600228237334866685051241 / 1267650600228229401496703205376 : ℚ), (633825300114118667433342525621 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d0 : LeanSuffixReflective.QInterval := ⟨(1291495555375912715765 / 1267650600228229401496703205376 : ℚ), (645747777687956357883 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ41_cJ40d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ40 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0))).widenAll cQ41_cJ40v cQ41_cJ40d0 cQ41_cJ40d1 cQ41_cJ40d2 (by
    norm_num [cJ0, cQ41_cJ40v, cQ41_cJ40d0, cQ41_cJ40d1, cQ41_cJ40d2])
private abbrev cQ42_cJ41v : LeanSuffixReflective.QInterval := ⟨(4361987963590405614796451321963 / 1267650600228229401496703205376 : ℚ), (4361987963590405614796451321971 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d0 : LeanSuffixReflective.QInterval := ⟨(-491225390995337811155433710375 / 633825300114114700748351602688 : ℚ), (-982450781990675622310867420737 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ42_cJ41d2 : LeanSuffixReflective.QInterval := ⟨(1000867878788477322821 / 1267650600228229401496703205376 : ℚ), (1000867878788477322827 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ41 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ39).add ((cJ40).mul (cJ38))).widenAll cQ42_cJ41v cQ42_cJ41d0 cQ42_cJ41d1 cQ42_cJ41d2 (by
    norm_num [cJ39, cJ40, cJ38, cQ42_cJ41v, cQ42_cJ41d0, cQ42_cJ41d1, cQ42_cJ41d2])
private abbrev cQ43_cJ42v : LeanSuffixReflective.QInterval := ⟨(12912022211080020467683762229437 / 1267650600228229401496703205376 : ℚ), (12912022211080020467683762229497 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d0 : LeanSuffixReflective.QInterval := ⟨(-8724539947605943414066676014443 / 1267650600228229401496703205376 : ℚ), (-2181134986901485853516669003581 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ43_cJ42d2 : LeanSuffixReflective.QInterval := ⟨(8888076988733632673003 / 1267650600228229401496703205376 : ℚ), (2222019247183408168263 / 316912650057057350374175801344 : ℚ), by norm_num⟩
@[simp] private abbrev cJ42 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).mul (cJ39)).mul (cJ41)).widenAll cQ43_cJ42v cQ43_cJ42d0 cQ43_cJ42d1 cQ43_cJ42d2 (by
    norm_num [cJ38, cJ39, cJ41, cQ43_cJ42v, cQ43_cJ42d0, cQ43_cJ42d1, cQ43_cJ42d2])
private abbrev cQ44_cJ43v : LeanSuffixReflective.QInterval := ⟨(1090496990897608228384157213131 / 316912650057057350374175801344 : ℚ), (545248495448804114192078606567 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d0 : LeanSuffixReflective.QInterval := ⟨(-982450777546643274264460859799 / 1267650600228229401496703205376 : ℚ), (-982450777546643274264460859781 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ44_cJ43d2 : LeanSuffixReflective.QInterval := ⟨(1000867878788483586577 / 1267650600228229401496703205376 : ℚ), (125108484848560448323 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ43 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ40).mul (cJ41)).widenAll cQ44_cJ43v cQ44_cJ43d0 cQ44_cJ43d1 cQ44_cJ43d2 (by
    norm_num [cJ40, cJ41, cQ44_cJ43v, cQ44_cJ43d0, cQ44_cJ43d1, cQ44_cJ43d2])
private abbrev cQ45_cJ44v : LeanSuffixReflective.QInterval := ⟨(4361987963590419264124052814051 / 1267650600228229401496703205376 : ℚ), (545248495448802408015506601761 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d0 : LeanSuffixReflective.QInterval := ⟨(-491225389884334335230209892699 / 633825300114114700748351602688 : ℚ), (-491225389884334335230209892669 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ45_cJ44d2 : LeanSuffixReflective.QInterval := ⟨(1000867878788480454709 / 1267650600228229401496703205376 : ℚ), (500433939394240227361 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ44 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ38).add (cJ39)).mul (((cJ35).mul (cJ35)).add ((cJ33).mul ((cJ38).mul (cJ39))))).widenAll cQ45_cJ44v cQ45_cJ44d0 cQ45_cJ44d1 cQ45_cJ44d2 (by
    norm_num [cJ38, cJ39, cJ35, cJ33, cQ45_cJ44v, cQ45_cJ44d0, cQ45_cJ44d1, cQ45_cJ44d2])
private abbrev cQ46_cJ45v : LeanSuffixReflective.QInterval := ⟨(2535301197907825211711859418647 / 1267650600228229401496703205376 : ℚ), (633825299476956302927964854665 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d0 : LeanSuffixReflective.QInterval := ⟨(-69149258806780231766333139 / 316912650057057350374175801344 : ℚ), (-276597035227120927065332539 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ46_cJ45d2 : LeanSuffixReflective.QInterval := ⟨(-1169590259453 / 1267650600228229401496703205376 : ℚ), (-146198782431 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ45 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul (cJ35)).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).widenAll cQ46_cJ45v cQ46_cJ45d0 cQ46_cJ45d1 cQ46_cJ45d2 (by
    norm_num [cJ35, cJ0, cQ46_cJ45v, cQ46_cJ45d0, cQ46_cJ45d1, cQ46_cJ45d2])
private abbrev cQ47_cJ46v : LeanSuffixReflective.QInterval := ⟨(124452856259808016820292024747 / 1267650600228229401496703205376 : ℚ), (31113214064952004205073006187 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d0 : LeanSuffixReflective.QInterval := ⟨(84091701383584801257500355463 / 1267650600228229401496703205376 : ℚ), (42045850691792400628750177733 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ47_cJ46d2 : LeanSuffixReflective.QInterval := ⟨(-85667957336362955177 / 1267650600228229401496703205376 : ℚ), (-85667957336362955175 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ46 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ42).invPos (by norm_num [cJ42])).widenAll cQ47_cJ46v cQ47_cJ46d0 cQ47_cJ46d1 cQ47_cJ46d2 (by
    norm_num [cJ42, NearOneScalarInterval.Jet3.invPos, cQ47_cJ46v, cQ47_cJ46d0, cQ47_cJ46d1, cQ47_cJ46d2])
private abbrev cQ48_cJ47v : LeanSuffixReflective.QInterval := ⟨(248905712269401400414698047285 / 1267650600228229401496703205376 : ℚ), (248905712269401400414698047289 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d0 : LeanSuffixReflective.QInterval := ⟨(168156247409549965701500534699 / 1267650600228229401496703205376 : ℚ), (168156247409549965701500534709 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ48_cJ47d2 : LeanSuffixReflective.QInterval := ⟨(-85667957307657338145 / 633825300114114700748351602688 : ℚ), (-171335914615314676285 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ47 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ46)).widenAll cQ48_cJ47v cQ48_cJ47d0 cQ48_cJ47d1 cQ48_cJ47d2 (by
    norm_num [cJ45, cJ46, cQ48_cJ47v, cQ48_cJ47d0, cQ48_cJ47d1, cQ48_cJ47d2])
private abbrev cQ49_cJ48v : LeanSuffixReflective.QInterval := ⟨(368395799729875886907117318887 / 1267650600228229401496703205376 : ℚ), (368395799729875886907117318889 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d0 : LeanSuffixReflective.QInterval := ⟨(41486902635974052526418934363 / 633825300114114700748351602688 : ℚ), (82973805271948105052837868729 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ49_cJ48d2 : LeanSuffixReflective.QInterval := ⟨(-84529238894719767201 / 1267650600228229401496703205376 : ℚ), (-84529238894719767199 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ48 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ43).invPos (by norm_num [cJ43])).widenAll cQ49_cJ48v cQ49_cJ48d0 cQ49_cJ48d1 cQ49_cJ48d2 (by
    norm_num [cJ43, NearOneScalarInterval.Jet3.invPos, cQ49_cJ48v, cQ49_cJ48d0, cQ49_cJ48d1, cQ49_cJ48d2])
private abbrev cQ50_cJ49v : LeanSuffixReflective.QInterval := ⟨(184197899679771401918069829725 / 316912650057057350374175801344 : ℚ), (736791598719085607672279318909 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d0 : LeanSuffixReflective.QInterval := ⟨(20733403458836514931035500157 / 158456325028528675187087900672 : ℚ), (165867227670692119448284001269 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ50_cJ49d2 : LeanSuffixReflective.QInterval := ⟨(-21132309744923776779 / 158456325028528675187087900672 : ℚ), (-169058477959390214225 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ49 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ45).mul (cJ48)).widenAll cQ50_cJ49v cQ50_cJ49d0 cQ50_cJ49d1 cQ50_cJ49d2 (by
    norm_num [cJ45, cJ48, cQ50_cJ49v, cQ50_cJ49d0, cQ50_cJ49d1, cQ50_cJ49d2])
private abbrev cQ51_cJ50v : LeanSuffixReflective.QInterval := ⟨(368395799729877039681105639059 / 1267650600228229401496703205376 : ℚ), (368395799729877039681105639063 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d0 : LeanSuffixReflective.QInterval := ⟨(41486902729805935462808090335 / 633825300114114700748351602688 : ℚ), (82973805459611870925616180677 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ51_cJ50d2 : LeanSuffixReflective.QInterval := ⟨(-42264619447360015855 / 633825300114114700748351602688 : ℚ), (-84529238894720031707 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ50 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ44).invPos (by norm_num [cJ44])).widenAll cQ51_cJ50v cQ51_cJ50d0 cQ51_cJ50d1 cQ51_cJ50d2 (by
    norm_num [cJ44, NearOneScalarInterval.Jet3.invPos, cQ51_cJ50v, cQ51_cJ50d0, cQ51_cJ50d1, cQ51_cJ50d2])
private abbrev cQ52_cJ51v : LeanSuffixReflective.QInterval := ⟨(368395799544711074484280879703 / 633825300114114700748351602688 : ℚ), (736791599089422148968561759417 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d0 : LeanSuffixReflective.QInterval := ⟨(82953709835132240840034033893 / 633825300114114700748351602688 : ℚ), (41476854917566120420017016951 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ52_cJ51d2 : LeanSuffixReflective.QInterval := ⟨(-169058477874415667905 / 1267650600228229401496703205376 : ℚ), (-169058477874415667897 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ51 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ35).mul ((NearOneScalarInterval.Jet3.rational (2 : ℚ)).add (((cJ0).mul (cJ0)).mul (cJ0)))).mul (cJ50)).widenAll cQ52_cJ51v cQ52_cJ51d0 cQ52_cJ51d1 cQ52_cJ51d2 (by
    norm_num [cJ35, cJ0, cJ50, cQ52_cJ51v, cQ52_cJ51d0, cQ52_cJ51d1, cQ52_cJ51d2])
private abbrev cQ53_cJ52v : LeanSuffixReflective.QInterval := ⟨(316912650216347445784992044905 / 316912650057057350374175801344 : ℚ), (158456325108173722892496022453 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d0 : LeanSuffixReflective.QInterval := ⟨(34574790892469343734972521 / 633825300114114700748351602688 : ℚ), (69149581784938687469945047 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ53_cJ52d2 : LeanSuffixReflective.QInterval := ⟨(146198782651 / 633825300114114700748351602688 : ℚ), (36549695663 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ52 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ53_cJ52v cQ53_cJ52d0 cQ53_cJ52d1 cQ53_cJ52d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ53_cJ52v, cQ53_cJ52d0, cQ53_cJ52d1, cQ53_cJ52d2])
private abbrev cQ54_cJ53v : LeanSuffixReflective.QInterval := ⟨(40192208129834037977724275 / 1267650600228229401496703205376 : ℚ), (10048052032458509494431069 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d0 : LeanSuffixReflective.QInterval := ⟨(2180998510487873759362812658393 / 1267650600228229401496703205376 : ℚ), (2180998510487873759362812658403 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ54_cJ53d2 : LeanSuffixReflective.QInterval := ⟨(576383406442447 / 79228162514264337593543950336 : ℚ), (9222134503079153 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ53 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ0).mul (cJ39)).mul (cJ52)).widenAll cQ54_cJ53v cQ54_cJ53d0 cQ54_cJ53d1 cQ54_cJ53d2 (by
    norm_num [cJ0, cJ39, cJ52, cQ54_cJ53v, cQ54_cJ53d0, cQ54_cJ53d1, cQ54_cJ53d2])
private abbrev cQ55_cJ54v : LeanSuffixReflective.QInterval := ⟨(250216969694693336939 / 1267650600228229401496703205376 : ℚ), (250216969694693336941 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d0 : LeanSuffixReflective.QInterval := ⟨(3394467246804956861539129 / 158456325028528675187087900672 : ℚ), (13577868987219827446156517 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ55_cJ54d2 : LeanSuffixReflective.QInterval := ⟨(-28706421251 / 633825300114114700748351602688 : ℚ), (-57412842501 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
@[simp] private abbrev cJ54 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ33).mul (cJ51)).widenAll cQ55_cJ54v cQ55_cJ54d0 cQ55_cJ54d1 cQ55_cJ54d2 (by
    norm_num [cJ33, cJ51, cQ55_cJ54v, cQ55_cJ54d0, cQ55_cJ54d1, cQ55_cJ54d2])
private abbrev cQ56_cJ55v : LeanSuffixReflective.QInterval := ⟨(1267650599803450524714447839907 / 1267650600228229401496703205376 : ℚ), (1267650599819379732593782416113 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d0 : LeanSuffixReflective.QInterval := ⟨(-46100801460354142027426517 / 1267650600228229401496703205376 : ℚ), (-44371591127101794082700503 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ56_cJ55d2 : LeanSuffixReflective.QInterval := ⟨(-194932637379 / 1267650600228229401496703205376 : ℚ), (-93810422043 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ55 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ53).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ53]) (by norm_num [cJ53])).widenAll cQ56_cJ55v cQ56_cJ55d0 cQ56_cJ55d1 cQ56_cJ55d2 (by
    norm_num [cJ53, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ56_cJ55v, cQ56_cJ55d0, cQ56_cJ55d1, cQ56_cJ55d2])
private abbrev cQ57_cJ56v : LeanSuffixReflective.QInterval := ⟨(19807040628566084398128751005 / 19807040628566084398385987584 : ℚ), (633825300114114700740428716055 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d0 : LeanSuffixReflective.QInterval := ⟨(-3573448637852961 / 1267650600228229401496703205376 : ℚ), (-859861078431459 / 316912650057057350374175801344 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ57_cJ56d2 : LeanSuffixReflective.QInterval := ⟨(7 / 1267650600228229401496703205376 : ℚ), (1 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ56 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ54).atanQuotient (1 / 4) (by norm_num) (by norm_num) (by norm_num [cJ54]) (by norm_num [cJ54])).widenAll cQ57_cJ56v cQ57_cJ56d0 cQ57_cJ56d1 cQ57_cJ56d2 (by
    norm_num [cJ54, NearOneScalarInterval.Jet3.atanQuotient, NearOneScalarInterval.Jet3.atanRemainderOne, cQ57_cJ56v, cQ57_cJ56d0, cQ57_cJ56d1, cQ57_cJ56d2])
private abbrev cQ58_cJ57v : LeanSuffixReflective.QInterval := ⟨(316912650216347445784992044905 / 316912650057057350374175801344 : ℚ), (158456325108173722892496022453 / 158456325028528675187087900672 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d0 : LeanSuffixReflective.QInterval := ⟨(34574790892469343734972521 / 633825300114114700748351602688 : ℚ), (69149581784938687469945047 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ58_cJ57d2 : LeanSuffixReflective.QInterval := ⟨(146198782651 / 633825300114114700748351602688 : ℚ), (36549695663 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ57 : NearOneScalarInterval.Jet3 centerBox :=
  ((cJ35).invPos (by norm_num [cJ35])).widenAll cQ58_cJ57v cQ58_cJ57d0 cQ58_cJ57d1 cQ58_cJ57d2 (by
    norm_num [cJ35, NearOneScalarInterval.Jet3.invPos, cQ58_cJ57v, cQ58_cJ57d0, cQ58_cJ57d1, cQ58_cJ57d2])
private abbrev cQ59_cJ58v : LeanSuffixReflective.QInterval := ⟨(23024737494690548043158400017 / 39614081257132168796771975168 : ℚ), (368395799915048768695367452713 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d0 : LeanSuffixReflective.QInterval := ⟨(165987804044795769628397774335 / 1267650600228229401496703205376 : ℚ), (82993902022398933989859329513 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ59_cJ58d2 : LeanSuffixReflective.QInterval := ⟨(-84529238852233552013 / 633825300114114700748351602688 : ℚ), (-84529238852233552005 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ58 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ33).mul (cJ39)).mul (cJ57)).mul (cJ55)).add ((cJ51).mul (cJ56))).widenAll cQ59_cJ58v cQ59_cJ58d0 cQ59_cJ58d1 cQ59_cJ58d2 (by
    norm_num [cJ33, cJ39, cJ57, cJ55, cJ51, cJ56, cQ59_cJ58v, cQ59_cJ58d0, cQ59_cJ58d1, cQ59_cJ58d2])
private abbrev cQ60_cJ59v : LeanSuffixReflective.QInterval := ⟨(1267650599909649210835198971123 / 1267650600228229401496703205376 : ℚ), (1267650599909649210835198971125 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d0 : LeanSuffixReflective.QInterval := ⟨(-17287395428856313083365153 / 633825300114114700748351602688 : ℚ), (-34574790857712626166730303 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d1 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private abbrev cQ60_cJ59d2 : LeanSuffixReflective.QInterval := ⟨(-146198782505 / 1267650600228229401496703205376 : ℚ), (-18274847813 / 158456325028528675187087900672 : ℚ), by norm_num⟩
@[simp] private abbrev cJ59 : NearOneScalarInterval.Jet3 centerBox :=
  ((NearOneScalarInterval.Jet3.rational (1 : ℚ)).add (((cJ5).mul (cJ4)).neg)).widenAll cQ60_cJ59v cQ60_cJ59d0 cQ60_cJ59d1 cQ60_cJ59d2 (by
    norm_num [cJ5, cJ4, cQ60_cJ59v, cQ60_cJ59d0, cQ60_cJ59d1, cQ60_cJ59d2])
private abbrev cQ61_cJ60v : LeanSuffixReflective.QInterval := ⟨(6568641883587039 / 633825300114114700748351602688 : ℚ), (13137283767174105 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d0 : LeanSuffixReflective.QInterval := ⟨(-2855851181678731 / 158456325028528675187087900672 : ℚ), (-11423404726491871 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d1 : LeanSuffixReflective.QInterval := ⟨(-171332359336827619029 / 79228162514264337593543950336 : ℚ), (-1370658874694620952219 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ61_cJ60d2 : LeanSuffixReflective.QInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
@[simp] private abbrev cJ60 : NearOneScalarInterval.Jet3 centerBox :=
  (((cJ8).mul (cJ20)).add ((((NearOneScalarInterval.Jet3.pi).mul (NearOneScalarInterval.Jet3.rational (1 / 2 : ℚ))).add ((cJ5).mul (cJ31))).neg)).widenAll cQ61_cJ60v cQ61_cJ60d0 cQ61_cJ60d1 cQ61_cJ60d2 (by
    norm_num [cJ8, cJ20, cJ5, cJ31, cQ61_cJ60v, cQ61_cJ60d0, cQ61_cJ60d1, cQ61_cJ60d2])
private abbrev cQ62_cJ61v : LeanSuffixReflective.QInterval := ⟨(-172476968213809 / 1267650600228229401496703205376 : ℚ), (-172459233983237 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d0 : LeanSuffixReflective.QInterval := ⟨(37556202218912749 / 1267650600228229401496703205376 : ℚ), (41405834015434285 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d1 : LeanSuffixReflective.QInterval := ⟨(8922917 / 633825300114114700748351602688 : ℚ), (17845907 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ62_cJ61d2 : LeanSuffixReflective.QInterval := ⟨(1014334027562014232757 / 633825300114114700748351602688 : ℚ), (1014334027562014232785 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ61 : NearOneScalarInterval.Jet3 centerBox :=
  (((((NearOneScalarInterval.Jet3.pi).mul ((cJ4).add ((cJ3).neg))).mul ((cJ8).add (cJ59))).add (((cJ8).mul (cJ8)).mul ((cJ58).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul (cJ59)).add (NearOneScalarInterval.Jet3.rational (1 : ℚ))).mul (cJ49))))).add ((((NearOneScalarInterval.Jet3.rational (2 : ℚ)).mul ((cJ59).mul (cJ59))).mul ((cJ31).add ((cJ8).mul (cJ22)))).neg)).widenAll cQ62_cJ61v cQ62_cJ61d0 cQ62_cJ61d1 cQ62_cJ61d2 (by
    norm_num [cJ4, cJ3, cJ8, cJ59, cJ58, cJ49, cJ31, cJ22, cQ62_cJ61v, cQ62_cJ61d0, cQ62_cJ61d1, cQ62_cJ61d2])
private abbrev cQ63_cJ62v : LeanSuffixReflective.QInterval := ⟨(-69441375058122007971 / 633825300114114700748351602688 : ℚ), (-69441375058122007953 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d0 : LeanSuffixReflective.QInterval := ⟨(-7536140675240608010728997 / 633825300114114700748351602688 : ℚ), (-15072281350481216021457933 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d1 : LeanSuffixReflective.QInterval := ⟨(126791753576375193253 / 158456325028528675187087900672 : ℚ), (1014334028611001546045 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ63_cJ62d2 : LeanSuffixReflective.QInterval := ⟨(-507167013972199281869 / 1267650600228229401496703205376 : ℚ), (-253583506986099640929 / 633825300114114700748351602688 : ℚ), by norm_num⟩
@[simp] private abbrev cJ62 : NearOneScalarInterval.Jet3 centerBox :=
  (((((cJ3).add ((cJ4).neg)).mul (cJ20)).add ((cJ59).mul (cJ22))).add (((cJ8).mul (cJ49)).neg)).widenAll cQ63_cJ62v cQ63_cJ62d0 cQ63_cJ62d1 cQ63_cJ62d2 (by
    norm_num [cJ3, cJ4, cJ20, cJ59, cJ22, cJ8, cJ49, cQ63_cJ62v, cQ63_cJ62d0, cQ63_cJ62d1, cQ63_cJ62d2])
private abbrev cQ64_cJ63v : LeanSuffixReflective.QInterval := ⟨(117263051713501642561011829815 / 316912650057057350374175801344 : ℚ), (234526103427003285122023659631 / 633825300114114700748351602688 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d0 : LeanSuffixReflective.QInterval := ⟨(-105632667626464109489703526939 / 1267650600228229401496703205376 : ℚ), (-105632667626464109489703526937 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d1 : LeanSuffixReflective.QInterval := ⟨(-215249259229318785961 / 633825300114114700748351602688 : ℚ), (-430498518458637571921 / 1267650600228229401496703205376 : ℚ), by norm_num⟩
private abbrev cQ64_cJ63d2 : LeanSuffixReflective.QInterval := ⟨(430498518458637571921 / 1267650600228229401496703205376 : ℚ), (215249259229318785961 / 633825300114114700748351602688 : ℚ), by norm_num⟩
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

theorem foldLoRange_lo : foldLoRange.lo = (9066731184973325561372827 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldLoRange_hi : foldLoRange.hi = (323666462671277647785920007 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [foldLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_lo : foldHiRange.lo = (-310070318175111377419724295 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem foldHiRange_hi : foldHiRange.hi = (-5667695060931757969823899 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [foldHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_lo : areaLoRange.lo = (-885062874977456766841839593 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaLoRange_hi : areaLoRange.hi = (-140231546666164249597227559 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaLoRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_lo : areaHiRange.lo = (140142300621659445021250087 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem areaHiRange_hi : areaHiRange.hi = (884973628932951962265862121 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [areaHiRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_lo : hFourRange.lo = (327981815621299533454967040771028171229 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem hFourRange_hi : hFourRange.hi = (327981815622413335348040834426575173155 / 327981815663069456811385861627845804032 : ℚ) := by norm_num [hFourRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_lo : shapeRange.lo = (81995453873997004642472016810122888507 / 81995453915767364202846465406961451008 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem shapeRange_hi : shapeRange.hi = (81995453875110823678422499299240736453 / 81995453915767364202846465406961451008 : ℚ) := by norm_num [shapeRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_lo : bSubARange.lo = (60679413606525205865883276390842311621 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem bSubARange_hi : bSubARange.hi = (60679416986896241394709822425708956731 / 163990907831534728405692930813922902016 : ℚ) := by norm_num [bSubARange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_lo : gapRange.lo = (-73303743936708485118701154065 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]
theorem gapRange_hi : gapRange.hi = (-70429920652587716672726356207 / 655963631326138913622771723255691608064 : ℚ) := by norm_num [gapRange, centeredRange, wholeModel, centerModel, tDisp, zeroDisp, e4LoDisp, e4HiDisp, e3LoDisp, e3HiDisp, e4FullDisp, e3FullDisp, wholeBox, centerBox, wJ60, cJ60, wJ61, cJ61, wJ8, cJ8, wJ35, cJ35, wJ63, cJ63, wJ62, cJ62]

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
end Band0Cell10
end
end NearOneScalarStress

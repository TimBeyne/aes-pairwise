import PairwiseIndependence.AesBounds.ActivityCertificate
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Exact rational certificate for the AES activity matrix

The sixteen activity patterns are ordered by their four bits with weights
`8, 4, 2, 1`. The two LDL factorizations below are checked entrywise by
`native_decide` over rational numbers. Positive rational diagonal entries
then certify both quadratic-form bounds. This replaces the paper's numerical
evaluation of the activity block with exact arithmetic.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

private def aesActivityPatternIndex (x : Fin 4 → Bool) : ℕ :=
  (if x 0 then 8 else 0) + (if x 1 then 4 else 0) +
    (if x 2 then 2 else 0) + (if x 3 then 1 else 0)

private def aesActivityRationalGram :
    Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ :=
  fun x y => ∏ i : Fin 4, if x i = y i then 1 else 1 / 16

private def aesActivityRationalCentered :
    Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ :=
  fun y x =>
    ((if 5 ≤ activityWeight x + activityWeight y then
        (256 : ℚ) ^ (activityWeight x + activityWeight y - 4)
      else 1) -
      (1 +
        (((256 : ℚ) ^ activityWeight x - 1) *
          ((256 : ℚ) ^ activityWeight y - 1)) /
            ((256 : ℚ) ^ 4 - 1))) /
      (16 : ℚ) ^ (activityWeight x + activityWeight y)

private def aesActivityRationalPlusL : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ :=
  fun x y =>
    match aesActivityPatternIndex x, aesActivityPatternIndex y with
    | 0, 0 => 1
    | 1, 0 => (1 / 16)
    | 1, 1 => 1
    | 2, 0 => (1 / 16)
    | 2, 1 => (-50000000 / 80510112047)
    | 2, 2 => 1
    | 3, 0 => (1 / 256)
    | 3, 1 => (67710112047 / 1288161792752)
    | 3, 2 => (22570037349 / 429120597584)
    | 3, 3 => 1
    | 4, 0 => (1 / 16)
    | 4, 1 => (-50000000 / 80510112047)
    | 4, 2 => (-50000000 / 80460112047)
    | 4, 3 => (-800000000 / 67710112047)
    | 4, 4 => 1
    | 5, 0 => (1 / 256)
    | 5, 1 => (67710112047 / 1288161792752)
    | 5, 2 => (-800000000 / 80460112047)
    | 5, 3 => (-12800000000 / 67710112047)
    | 5, 4 => (3230006591 / 63680105456)
    | 5, 5 => 1
    | 6, 0 => (1 / 256)
    | 6, 1 => (-803125000 / 80510112047)
    | 6, 2 => (67660112047 / 1287361792752)
    | 6, 3 => (-12800000000 / 67710112047)
    | 6, 4 => (3230006591 / 63680105456)
    | 6, 5 => (-750000000 / 3230006591)
    | 6, 6 => 1
    | 7, 0 => (1 / 4096)
    | 7, 1 => (-3209089887953 / 20610588684032)
    | 7, 2 => (-3209089887953 / 20597788684032)
    | 7, 3 => (7266065610653617 / 88089230730457872)
    | 7, 4 => (-1168097903098109 / 7531480806884096)
    | 7, 5 => (1252835107762403 / 12606483164198448)
    | 7, 6 => (1252835107762403 / 9679287164198448)
    | 7, 7 => 1
    | 8, 0 => (1 / 16)
    | 8, 1 => (-50000000 / 80510112047)
    | 8, 2 => (-50000000 / 80460112047)
    | 8, 3 => (-800000000 / 67710112047)
    | 8, 4 => (-50000000 / 67660112047)
    | 8, 5 => (-800000000 / 54910112047)
    | 8, 6 => (-800000000 / 42160112047)
    | 8, 7 => (-131435982886400000000 / 762119733481432755661)
    | 8, 8 => 1
    | 9, 0 => (1 / 256)
    | 9, 1 => (67710112047 / 1288161792752)
    | 9, 2 => (-800000000 / 80460112047)
    | 9, 3 => (-12800000000 / 67710112047)
    | 9, 4 => (-800000000 / 67660112047)
    | 9, 5 => (-12800000000 / 54910112047)
    | 9, 6 => (-12800000000 / 42160112047)
    | 9, 7 => (143930930918432000000 / 2286359200444298266983)
    | 9, 8 => (1579666780016508120891 / 28782188567876129934256)
    | 9, 9 => 1
    | 10, 0 => (1 / 256)
    | 10, 1 => (-803125000 / 80510112047)
    | 10, 2 => (67660112047 / 1287361792752)
    | 10, 3 => (-12800000000 / 67710112047)
    | 10, 4 => (-800000000 / 67660112047)
    | 10, 5 => (-12800000000 / 54910112047)
    | 10, 6 => (-12800000000 / 42160112047)
    | 10, 7 => (143930930918432000000 / 2286359200444298266983)
    | 10, 8 => (1579666780016508120891 / 28782188567876129934256)
    | 10, 9 => (-4976966969281750000000 / 11213014100148573088019)
    | 10, 10 => 1
    | 11, 0 => (1 / 4096)
    | 11, 1 => (-3209089887953 / 20610588684032)
    | 11, 2 => (-3209089887953 / 20597788684032)
    | 11, 3 => (7266065610653617 / 88089230730457872)
    | 11, 4 => (-51456775000000 / 323618315920801)
    | 11, 5 => (17578919375000 / 787905197762403)
    | 11, 6 => (17578919375000 / 604955447762403)
    | 11, 7 => (-202775320829894000000 / 2286359200444298266983)
    | 11, 8 => (-558026174852428443153763 / 3223605119602126552636672)
    | 11, 9 => (3560245919350571869717 / 25629746514625309915472)
    | 11, 10 => (24921721435454003088019 / 99776754093869169408304)
    | 11, 11 => 1
    | 12, 0 => (1 / 256)
    | 12, 1 => (-803125000 / 80510112047)
    | 12, 2 => (-803125000 / 80460112047)
    | 12, 3 => (-50000000 / 263463471)
    | 12, 4 => (54860112047 / 1082561792752)
    | 12, 5 => (-12800000000 / 54910112047)
    | 12, 6 => (-12800000000 / 42160112047)
    | 12, 7 => (143930930918432000000 / 2286359200444298266983)
    | 12, 8 => (1579666780016508120891 / 28782188567876129934256)
    | 12, 9 => (-4976966969281750000000 / 11213014100148573088019)
    | 12, 10 => (-4976966969281750000000 / 6236047130866823088019)
    | 12, 11 => (8207041263191232000000 / 36898472152491213616133)
    | 12, 12 => 1
    | 13, 0 => (1 / 4096)
    | 13, 1 => (-3209089887953 / 20610588684032)
    | 13, 2 => (-12850000000 / 80460112047)
    | 13, 3 => (14993914375000 / 1835192306884539)
    | 13, 4 => (-12910299334079199 / 82846288875725056)
    | 13, 5 => (1069167907762403 / 12606483164198448)
    | 13, 6 => (17578919375000 / 604955447762403)
    | 13, 7 => (-202775320829894000000 / 2286359200444298266983)
    | 13, 8 => (-558026174852428443153763 / 3223605119602126552636672)
    | 13, 9 => (3560245919350571869717 / 25629746514625309915472)
    | 13, 10 => (856794208456589375000 / 6236047130866823088019)
    | 13, 11 => (-6240917684627096000000 / 36898472152491213616133)
    | 13, 12 => (4142808516958461321701 / 2866890146675861147216)
    | 13, 13 => 1
    | 14, 0 => (1 / 4096)
    | 14, 1 => (-25700390625 / 161020224094)
    | 14, 2 => (-3209139887953 / 20597788684032)
    | 14, 3 => (14993914375000 / 1835192306884539)
    | 14, 4 => (-12910299334079199 / 82846288875725056)
    | 14, 5 => (6144560000000 / 787905197762403)
    | 14, 6 => (886218157762403 / 9679287164198448)
    | 14, 7 => (-202775320829894000000 / 2286359200444298266983)
    | 14, 8 => (-558026174852428443153763 / 3223605119602126552636672)
    | 14, 9 => (545733772876480000000 / 11213014100148573088019)
    | 14, 10 => (19944754466172253088019 / 99776754093869169408304)
    | 14, 11 => (-6240917684627096000000 / 36898472152491213616133)
    | 14, 12 => (4142808516958461321701 / 2866890146675861147216)
    | 14, 13 => (-87896975865956000000 / 91283658301285321701)
    | 14, 14 => 1
    | 15, 0 => (1 / 65536)
    | 15, 1 => (80560112047 / 329769418944512)
    | 15, 2 => (80560112047 / 329564618944512)
    | 15, 3 => (313463471 / 67446648576)
    | 15, 4 => (80560112047 / 277135818944512)
    | 15, 5 => (80560112047 / 14056988684032)
    | 15, 6 => (80560112047 / 10792988684032)
    | 15, 7 => (827226367838746755661 / 12193915735702924090576)
    | 15, 8 => (586200441770604506846237 / 51577681913634024842186752)
    | 15, 9 => (19651269811960851 / 4525018734581977856)
    | 15, 10 => (12466156379343793088019 / 1596428065501906710532864)
    | 15, 11 => (47960555031484849616133 / 590375554439859417858128)
    | 15, 12 => (-23315687946760085461289 / 504572665814951561910016)
    | 15, 13 => (87454701086496440567 / 486846177606855049072)
    | 15, 14 => (262364103259489321701 / 54186918965269147216)
    | 15, 15 => 1
    | _, _ => 0

private def aesActivityRationalPlusD : (Fin 4 → Bool) → ℚ :=
  fun x => match aesActivityPatternIndex x with
    | 0 => (4783 / 50000000)
    | 1 => (4106015714397 / 43118103040000000)
    | 2 => (19626876511960851 / 206105886840320000000)
    | 3 => (280784422953334467 / 3515355935408128000000)
    | 4 => (5501511370653617 / 57779295613440000000)
    | 5 => (40183165085882553 / 521667423895552000000)
    | 6 => (30852727835882553 / 423363423895552000000)
    | 7 => (6859077601332894800949 / 79603672294012171059200000)
    | 8 => (180685585395198882436654713 / 1951026517712467854492160000000)
    | 9 => (15499603621452070648118519453 / 235783688748041256421425152000000)
    | 10 => (77580061923460574572816675077 / 1469712184134673771792826368000000)
    | 11 => (23410963774699035587873869002489 / 292945827162052282908148970291200000)
    | 12 => (73560681194556650940482725539 / 4836356541971328351093784576000000)
    | 13 => (57916718309679731616452575833 / 1202460880976315111321265766400000)
    | 14 => (716249166833061502234858611 / 204198087012114255974288588800000)
    | 15 => (139447882676296543213259042313 / 12800207465475823092179119636480000)
    | _ => 0

private theorem aesActivityRationalPlusD_nonneg (x : Fin 4 → Bool) :
    0 ≤ aesActivityRationalPlusD x := by
  have h : ∀ x : Fin 4 → Bool,
      0 ≤ aesActivityRationalPlusD x := by native_decide
  exact h x

private theorem aesActivityRationalPlus_factor :
    (9566 / 100000000 : ℚ) • aesActivityRationalGram
      + aesActivityRationalCentered =
      aesActivityRationalPlusL * Matrix.diagonal aesActivityRationalPlusD * aesActivityRationalPlusLᵀ := by
  have h : ∀ x y : Fin 4 → Bool,
      ((9566 / 100000000 : ℚ) • aesActivityRationalGram
        + aesActivityRationalCentered) x y =
        (aesActivityRationalPlusL * Matrix.diagonal aesActivityRationalPlusD * aesActivityRationalPlusLᵀ) x y := by
    native_decide
  ext x y
  exact h x y

private def aesActivityRationalMinusL : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ :=
  fun x y =>
    match aesActivityPatternIndex x, aesActivityPatternIndex y with
    | 0, 0 => 1
    | 1, 0 => (1 / 16)
    | 1, 1 => 1
    | 2, 0 => (1 / 16)
    | 2, 1 => (50000000 / 80610112047)
    | 2, 2 => 1
    | 3, 0 => (1 / 256)
    | 3, 1 => (93410112047 / 1289761792752)
    | 3, 2 => (93410112047 / 1290561792752)
    | 3, 3 => 1
    | 4, 0 => (1 / 16)
    | 4, 1 => (50000000 / 80610112047)
    | 4, 2 => (50000000 / 80660112047)
    | 4, 3 => (800000000 / 93410112047)
    | 4, 4 => 1
    | 5, 0 => (1 / 256)
    | 5, 1 => (93410112047 / 1289761792752)
    | 5, 2 => (800000000 / 80660112047)
    | 5, 3 => (12800000000 / 93410112047)
    | 5, 4 => (106210112047 / 1495361792752)
    | 5, 5 => 1
    | 6, 0 => (1 / 256)
    | 6, 1 => (803125000 / 80610112047)
    | 6, 2 => (93460112047 / 1290561792752)
    | 6, 3 => (12800000000 / 93410112047)
    | 6, 4 => (106210112047 / 1495361792752)
    | 6, 5 => (12750000000 / 106210112047)
    | 6, 6 => 1
    | 7, 0 => (1 / 4096)
    | 7, 1 => (3370210112047 / 20636188684032)
    | 7, 2 => (3370210112047 / 20648988684032)
    | 7, 3 => (15504342791960851 / 364572941791373616)
    | 7, 4 => (18619714965920801 / 114437047275725056)
    | 7, 5 => (15004342791960851 / 414530420191373616)
    | 7, 6 => (2143477541708693 / 66327536027339088)
    | 7, 7 => 1
    | 8, 0 => (1 / 16)
    | 8, 1 => (50000000 / 80610112047)
    | 8, 2 => (50000000 / 80660112047)
    | 8, 3 => (800000000 / 93410112047)
    | 8, 4 => (50000000 / 93460112047)
    | 8, 5 => (800000000 / 106210112047)
    | 8, 6 => (800000000 / 118960112047)
    | 8, 7 => (2741800675315200000000 / 15939305839977500362673)
    | 8, 8 => 1
    | 9, 0 => (1 / 256)
    | 9, 1 => (93410112047 / 1289761792752)
    | 9, 2 => (800000000 / 80660112047)
    | 9, 3 => (12800000000 / 93410112047)
    | 9, 4 => (800000000 / 93460112047)
    | 9, 5 => (12800000000 / 106210112047)
    | 9, 6 => (12800000000 / 118960112047)
    | 9, 7 => (-349546546516192000000 / 15939305839977500362673)
    | 9, 8 => (43258625569016300846237 / 579119000490976813539792)
    | 9, 9 => 1
    | 10, 0 => (1 / 256)
    | 10, 1 => (803125000 / 80610112047)
    | 10, 2 => (93460112047 / 1290561792752)
    | 10, 3 => (12800000000 / 93410112047)
    | 10, 4 => (800000000 / 93460112047)
    | 10, 5 => (12800000000 / 106210112047)
    | 10, 6 => (12800000000 / 118960112047)
    | 10, 7 => (-349546546516192000000 / 15939305839977500362673)
    | 10, 8 => (43258625569016300846237 / 579119000490976813539792)
    | 10, 9 => (3838364878330250000000 / 40033302409016300846237)
    | 10, 10 => 1
    | 11, 0 => (1 / 4096)
    | 11, 1 => (3370210112047 / 20636188684032)
    | 11, 2 => (3370210112047 / 20648988684032)
    | 11, 3 => (15504342791960851 / 364572941791373616)
    | 11, 4 => (70988025000000 / 447019715920801)
    | 11, 5 => (-486341629375000 / 25908151261960851)
    | 11, 6 => (-69477375625000 / 4145471001708693)
    | 11, 7 => (-1305789660841686000000 / 15939305839977500362673)
    | 11, 8 => (1675321170881560300846237 / 9265904007855629016636672)
    | 11, 9 => (23809217050445410846237 / 640532838544260813539792)
    | 11, 10 => (23809217050445410846237 / 701946676597544813539792)
    | 11, 11 => 1
    | 12, 0 => (1 / 256)
    | 12, 1 => (803125000 / 80610112047)
    | 12, 2 => (803125000 / 80660112047)
    | 12, 3 => (50000000 / 363463471)
    | 12, 4 => (106260112047 / 1495361792752)
    | 12, 5 => (12800000000 / 106210112047)
    | 12, 6 => (12800000000 / 118960112047)
    | 12, 7 => (-349546546516192000000 / 15939305839977500362673)
    | 12, 8 => (43258625569016300846237 / 579119000490976813539792)
    | 12, 9 => (3838364878330250000000 / 40033302409016300846237)
    | 12, 10 => (3838364878330250000000 / 43871667287346550846237)
    | 12, 11 => (-1258820407021248000000 / 39016632505521722846237)
    | 12, 12 => 1
    | 13, 0 => (1 / 4096)
    | 13, 1 => (3370210112047 / 20636188684032)
    | 13, 2 => (12850000000 / 80660112047)
    | 13, 3 => (-259945229375000 / 22785808861960851)
    | 13, 4 => (18680937365920801 / 114437047275725056)
    | 13, 5 => (18126685191960851 / 414530420191373616)
    | 13, 6 => (-69477375625000 / 4145471001708693)
    | 13, 7 => (-1305789660841686000000 / 15939305839977500362673)
    | 13, 8 => (1675321170881560300846237 / 9265904007855629016636672)
    | 13, 9 => (23809217050445410846237 / 640532838544260813539792)
    | 13, 10 => (-1014005334910680625000 / 43871667287346550846237)
    | 13, 11 => (-4933711057263656000000 / 39016632505521722846237)
    | 13, 12 => (7443932662316944282079 / 226102657193877188513264)
    | 13, 13 => 1
    | 14, 0 => (1 / 4096)
    | 14, 1 => (8566796875 / 53740074698)
    | 14, 2 => (3370260112047 / 20648988684032)
    | 14, 3 => (-259945229375000 / 22785808861960851)
    | 14, 4 => (18680937365920801 / 114437047275725056)
    | 14, 5 => (-291957520000000 / 25908151261960851)
    | 14, 6 => (3033832991708693 / 66327536027339088)
    | 14, 7 => (-1305789660841686000000 / 15939305839977500362673)
    | 14, 8 => (1675321170881560300846237 / 9265904007855629016636672)
    | 14, 9 => (-774107530015040000000 / 40033302409016300846237)
    | 14, 10 => (27647581928775660846237 / 701946676597544813539792)
    | 14, 11 => (-4933711057263656000000 / 39016632505521722846237)
    | 14, 12 => (7443932662316944282079 / 226102657193877188513264)
    | 14, 13 => (-1771927980608276000000 / 12359488094009048282079)
    | 14, 14 => 1
    | 15, 0 => (1 / 65536)
    | 15, 1 => (80560112047 / 330179018944512)
    | 15, 2 => (80560112047 / 330383818944512)
    | 15, 3 => (313463471 / 93046648576)
    | 15, 4 => (80560112047 / 382812618944512)
    | 15, 5 => (80560112047 / 27189788684032)
    | 15, 6 => (80560112047 / 30453788684032)
    | 15, 7 => (17256232001088498362673 / 255028893439640005802768)
    | 15, 8 => (-4818023638424417947461289 / 444763392377070192798560256)
    | 15, 9 => (6550423270653617 / 1504143803047325952)
    | 15, 10 => (133894470548926722538711 / 33693440476682151049910016)
    | 15, 11 => (146995317090233956538711 / 1872798360265042696619376)
    | 15, 12 => (186297856714155658538711 / 32558782635918315145910016)
    | 15, 13 => (53365387877180396846237 / 593255428512434317539792)
    | 15, 14 => (53365387877180396846237 / 508202885443237069539792)
    | 15, 15 => 1
    | _, _ => 0

private def aesActivityRationalMinusD : (Fin 4 → Bool) → ℚ :=
  fun x => match aesActivityPatternIndex x with
    | 0 => (4783 / 50000000)
    | 1 => (4111115714397 / 43118103040000000)
    | 2 => (6558554370653617 / 68787295613440000000)
    | 3 => (1162076251960003401 / 10572282206224384000000)
    | 4 => (22798005511960851 / 239129886840320000000)
    | 5 => (1321315714360003401 / 12250003806224384000000)
    | 6 => (1479933147610003401 / 13921171806224384000000)
    | 7 => (47817917519932501088019 / 545485979744338129715200000)
    | 8 => (26487419090018521323225390363 / 285632360652396806499100160000000)
    | 9 => (166012540461155746343527212057 / 1581380950674027352172658688000000)
    | 10 => (545789118236619615566331636171 / 5247245013354584584517976064000000)
    | 11 => (24754872408337488519951989444721 / 294417775343978860160920374476800000)
    | 12 => (527409163751433047907357636171 / 5113988055763743256901976064000000)
    | 13 => (7841721111022599763114771814907 / 94834327947890786728993724825600000)
    | 14 => (2239162146090279237268154604969 / 27647706853682414531049108275200000)
    | 15 => (338894442059606701916810766560257 / 3637857954519229463413807351070720000)
    | _ => 0

private theorem aesActivityRationalMinusD_nonneg (x : Fin 4 → Bool) :
    0 ≤ aesActivityRationalMinusD x := by
  have h : ∀ x : Fin 4 → Bool,
      0 ≤ aesActivityRationalMinusD x := by native_decide
  exact h x

private theorem aesActivityRationalMinus_factor :
    (9566 / 100000000 : ℚ) • aesActivityRationalGram
      - aesActivityRationalCentered =
      aesActivityRationalMinusL * Matrix.diagonal aesActivityRationalMinusD * aesActivityRationalMinusLᵀ := by
  have h : ∀ x y : Fin 4 → Bool,
      ((9566 / 100000000 : ℚ) • aesActivityRationalGram
        - aesActivityRationalCentered) x y =
        (aesActivityRationalMinusL * Matrix.diagonal aesActivityRationalMinusD * aesActivityRationalMinusLᵀ) x y := by
    native_decide
  ext x y
  exact h x y

private theorem rationalLDL_posSemidef
    (L : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ)
    (d : (Fin 4 → Bool) → ℚ) (hd : ∀ x, 0 ≤ d x) :
    ((L.map (fun q : ℚ => (q : ℝ))) *
      Matrix.diagonal (fun x => (d x : ℝ)) *
      (L.map (fun q : ℚ => (q : ℝ)))ᵀ).PosSemidef := by
  have hdiag :
      (Matrix.diagonal (fun x => (d x : ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (by
      intro x
      change (0 : ℝ) ≤ (d x : ℝ)
      exact_mod_cast hd x)
  simpa only [Matrix.conjTranspose, star_trivial,
    Matrix.transpose_transpose] using
    hdiag.conjTranspose_mul_mul_same
      ((L.map (fun q : ℚ => (q : ℝ)))ᵀ)

private theorem aesActivityRationalPlus_real_posSemidef :
    (((9566 / 100000000 : ℚ) • aesActivityRationalGram +
      aesActivityRationalCentered).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  rw [aesActivityRationalPlus_factor]
  simpa only [Matrix.map_mul_ratCast, Matrix.diagonal_map,
    Matrix.transpose_map, Rat.cast_zero] using
    rationalLDL_posSemidef aesActivityRationalPlusL
      aesActivityRationalPlusD aesActivityRationalPlusD_nonneg

private theorem aesActivityRationalMinus_real_posSemidef :
    (((9566 / 100000000 : ℚ) • aesActivityRationalGram -
      aesActivityRationalCentered).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  rw [aesActivityRationalMinus_factor]
  simpa only [Matrix.map_mul_ratCast, Matrix.diagonal_map,
    Matrix.transpose_map, Rat.cast_zero] using
    rationalLDL_posSemidef aesActivityRationalMinusL
      aesActivityRationalMinusD aesActivityRationalMinusD_nonneg

private theorem aesActivityRationalGram_cast :
    aesActivityRationalGram.map (fun q : ℚ => (q : ℝ)) =
      booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) := by
  ext x y
  simp [aesActivityRationalGram, booleanActivityGramKernel]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> norm_num

private theorem aesActivityRationalCentered_cast :
    aesActivityRationalCentered.map (fun q : ℚ => (q : ℝ)) =
      aesRationalCenteredActivityMatrix := by
  ext y x
  simp only [Matrix.map_apply, aesActivityRationalCentered,
    aesRationalCenteredActivityMatrix]
  split_ifs <;> push_cast <;> ring

private theorem aesActivityRationalPlus_cast :
    ((9566 / 100000000 : ℚ) • aesActivityRationalGram +
      aesActivityRationalCentered).map (fun q : ℚ => (q : ℝ)) =
      (9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) +
        aesRationalCenteredActivityMatrix := by
  ext x y
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  push_cast
  have hG := congrArg (fun K : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ => K x y)
    aesActivityRationalGram_cast
  have hD := congrArg (fun K : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ => K x y)
    aesActivityRationalCentered_cast
  simp only [Matrix.map_apply] at hG hD
  rw [hG, hD]

private theorem aesActivityRationalMinus_cast :
    ((9566 / 100000000 : ℚ) • aesActivityRationalGram -
      aesActivityRationalCentered).map (fun q : ℚ => (q : ℝ)) =
      (9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) -
        aesRationalCenteredActivityMatrix := by
  ext x y
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  push_cast
  have hG := congrArg (fun K : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ => K x y)
    aesActivityRationalGram_cast
  have hD := congrArg (fun K : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ => K x y)
    aesActivityRationalCentered_cast
  simp only [Matrix.map_apply] at hG hD
  rw [hG, hD]

/-- The two exact rational LDL certificates establish the finite
quadratic-form premises for the AES activity block. -/
theorem aesActivityRational_posSemidef_bounds :
    Matrix.PosSemidef
      ((9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) +
        aesRationalCenteredActivityMatrix) ∧
    Matrix.PosSemidef
      ((9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) -
        aesRationalCenteredActivityMatrix) := by
  constructor
  · simpa only [aesActivityRationalPlus_cast] using
      aesActivityRationalPlus_real_posSemidef
  · simpa only [aesActivityRationalMinus_cast] using
      aesActivityRationalMinus_real_posSemidef

/-- The rational certificate lies below the paper's rounded exponent. -/
theorem aesActivityRational_le_paper :
    (9566 / 100000000 : ℝ) ≤ (2 : ℝ) ^ (-(13.351 : ℝ)) := by
  have hmid : (9566 / 100000000 : ℝ) ≤ (2 : ℝ) ^ (-(1709 / 128 : ℝ)) := by
    apply (Real.rpow_le_rpow_iff
      (by norm_num)
      (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (0 : ℝ) < 128)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : (-(1709 / 128 : ℝ)) * (128 : ℝ) = -(1709 : ℝ) := by norm_num
    rw [hexp]
    norm_num
  exact hmid.trans (Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : -(1709 / 128 : ℝ) ≤ -(13.351 : ℝ)))

/-- The first displayed block estimate of Theorem 4 for the concrete
independently keyed AES superbox. This block is the activity-space part
of the difference-distribution matrix. -/
theorem theorem4_aesIndependentSuperbox_activityBlock :
    ‖activityTruncatedOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4))‖ ≤
      (2 : ℝ) ^ (-(13.351 : ℝ)) := by
  let u : AesByte := aesByteOfNat 1
  have hu : u ≠ 0 := by decide
  apply aesIndependentSuperbox_activityBlock_le_of_canonical_bound u hu
  exact (aesActivityCanonical_norm_le_of_posSemidef u hu
    aesActivityRational_posSemidef_bounds.1
    aesActivityRational_posSemidef_bounds.2).trans
      aesActivityRational_le_paper

end PairwiseIndependence

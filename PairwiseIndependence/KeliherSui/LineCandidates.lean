import PairwiseIndependence.KeliherSui.LineGeometry

/-!
# The finite exceptional affine lines

If no mixed input/output pair prunes, all five count-four positions
coincide. The 63-pair certificate restricts their five coordinate values
to the short lists below. A candidate is retained only if it belongs to
the actual MixColumns graph. We check its complete five-factor sum.
-/

namespace PairwiseIndependence

def keliherSuiInverseSpecials (specials : Array (Fin 256)) : Array (Fin 256) :=
  Array.ofFn (fun z : Fin 256 =>
    ⟨(∑ a : Fin 256, if specials[a.val]! = z then a.val else 0) % 256,
      Nat.mod_lt _ (by omega)⟩)

def keliherSuiRowEndpoints : Array (Fin 256) :=
  keliherSuiInverseSpecials (keliherSuiRowSpecials keliherSuiCounts)

def keliherSuiColumnEndpoints : Array (Fin 256) :=
  keliherSuiInverseSpecials (keliherSuiColumnSpecials keliherSuiCounts)

def KeliherSuiEndpointsCheck (rs cs re ce : Array (Fin 256)) : Prop :=
  ∀ a : Fin 256, a ≠ 0 → re[(rs[a.val]!).val]! = a ∧ ce[(cs[a.val]!).val]! = a

instance (rs cs re ce : Array (Fin 256)) : Decidable (KeliherSuiEndpointsCheck rs cs re ce) :=
  inferInstanceAs (Decidable (∀ a : Fin 256, a ≠ 0 →
    re[(rs[a.val]!).val]! = a ∧ ce[(cs[a.val]!).val]! = a))

theorem keliherSuiEndpoints_spec :
    KeliherSuiEndpointsCheck (keliherSuiRowSpecials keliherSuiCounts)
      (keliherSuiColumnSpecials keliherSuiCounts)
      keliherSuiRowEndpoints keliherSuiColumnEndpoints := by native_decide

def keliherSuiLineInput (s : Fin 56) (i : Fin 5) : Bool :=
  match keliherSuiLineFree s i with
  | Sum.inl _ => true
  | Sum.inr _ => false

def keliherSuiLineRatioWith (M : Array (Array (Fin 256)))
    (s : Fin 56) (i j : Fin 5) : Fin 256 :=
  (M[(keliherSuiInverse (keliherSuiLineCoefficient s i)).val]!)[
    (keliherSuiLineCoefficient s j).val]!

def keliherSuiLineRatio (s : Fin 56) (i j : Fin 5) : Fin 256 :=
  keliherSuiLineRatioWith keliherSuiMultiplication s i j

def keliherSuiLineOptionsWith (M : Array (Array (Fin 256)))
    (s : Fin 56) (i : Fin 5) (x y : Fin 256) : List (Fin 256) :=
  if keliherSuiLineInput s i then
    (keliherSuiExceptionalPairs.filter (fun e =>
      (M[(keliherSuiLineRatioWith M s i 1).val]!)[e.2.val]! = y)).map Prod.fst
  else
    (keliherSuiExceptionalPairs.filter (fun e => e.1 = x)).map
      (fun e => (M[(keliherSuiLineRatioWith M s 0 i).val]!)[e.2.val]!)

def keliherSuiLineOptions (s : Fin 56) (i : Fin 5) (x y : Fin 256) : List (Fin 256) :=
  keliherSuiLineOptionsWith keliherSuiMultiplication s i x y

def keliherSuiLineCompatible (s : Fin 56) (z : Fin 5 → Fin 256) : Prop :=
  mdsGraphCoordinate aesMixColumnEquiv
    (keliherSuiLineReconstruct s (fun i => aesByteFinEquiv (z i.castSucc)))
    (keliherSuiLineFree s 4) = aesByteFinEquiv (z 4)

def keliherSuiLineCompatibleFast (basis : Array (Array (Array (State AesByte 4))))
    (s : Fin 56) (z : Fin 5 → Fin 256) : Prop :=
  mdsGraphCoordinate aesMixColumnEquiv
    (∑ j : Fin 4, ((basis[s.val]!)[j.val]!)[(z j.castSucc).val]!)
    (keliherSuiLineFree s 4) = aesByteFinEquiv (z 4)

instance (basis : Array (Array (Array (State AesByte 4))))
    (s : Fin 56) (z : Fin 5 → Fin 256) :
    Decidable (keliherSuiLineCompatibleFast basis s z) :=
  inferInstanceAs (Decidable (_ = _))

theorem keliherSuiLineCompatibleFast_iff (s : Fin 56) (z : Fin 5 → Fin 256) :
    keliherSuiLineCompatibleFast (keliherSuiBasisTable keliherSuiMultiplication) s z ↔
      keliherSuiLineCompatible s z := by
  simp only [keliherSuiLineCompatibleFast, keliherSuiLineCompatible,
    keliherSuiLineReconstruct, keliherSuiBasisTable_get]

def keliherSuiLineFiveSum
    (C : Array (Array Nat)) (M : Array (Array (Fin 256)))
    (re ce : Array (Fin 256)) (s : Fin 56) (z : Fin 5 → Fin 256) : Nat :=
  ∑ t : Fin 256, ∏ i : Fin 5,
    let u := keliherSuiXor (z i) ((M[(keliherSuiLineCoefficient s i).val]!)[t.val]!)
    if keliherSuiLineInput s i then (C[(re[(z i).val]!).val]!)[u.val]!
    else (C[u.val]!)[(ce[(z i).val]!).val]!

def KeliherSuiLineCandidateCheck
    (C : Array (Array Nat)) (M : Array (Array (Fin 256)))
    (re ce : Array (Fin 256)) (basis : Array (Array (Array (State AesByte 4)))) : Prop :=
  ∀ s : Fin 56, ∀ e ∈ keliherSuiExceptionalPairs,
    let y := (M[(keliherSuiLineRatioWith M s 0 1).val]!)[e.2.val]!
    ∀ z ∈ keliherSuiLineOptionsWith M s 2 e.1 y,
    ∀ w ∈ keliherSuiLineOptionsWith M s 3 e.1 y,
    ∀ u ∈ keliherSuiLineOptionsWith M s 4 e.1 y,
    keliherSuiLineCompatibleFast basis s ![e.1, y, z, w, u] →
    keliherSuiLineFiveSum C M re ce s ![e.1, y, z, w, u] ≤ 3392

instance (C : Array (Array Nat)) (M : Array (Array (Fin 256)))
    (re ce : Array (Fin 256)) (basis : Array (Array (Array (State AesByte 4)))) :
    Decidable (KeliherSuiLineCandidateCheck C M re ce basis) :=
  inferInstanceAs (Decidable (∀ s : Fin 56, ∀ e ∈ keliherSuiExceptionalPairs,
    let y := (M[(keliherSuiLineRatioWith M s 0 1).val]!)[e.2.val]!
    ∀ z ∈ keliherSuiLineOptionsWith M s 2 e.1 y,
    ∀ w ∈ keliherSuiLineOptionsWith M s 3 e.1 y,
    ∀ u ∈ keliherSuiLineOptionsWith M s 4 e.1 y,
    keliherSuiLineCompatibleFast basis s ![e.1, y, z, w, u] →
    keliherSuiLineFiveSum C M re ce s ![e.1, y, z, w, u] ≤ 3392))

theorem keliherSuiLineCandidates_certificate :
    KeliherSuiLineCandidateCheck keliherSuiCounts keliherSuiMultiplication
      keliherSuiRowEndpoints keliherSuiColumnEndpoints
      (keliherSuiBasisTable keliherSuiMultiplication) := by
  native_decide

end PairwiseIndependence

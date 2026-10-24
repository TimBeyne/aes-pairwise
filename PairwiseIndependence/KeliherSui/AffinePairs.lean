import PairwiseIndependence.KeliherSui.PackedSupport
import PairwiseIndependence.KeliherSui.Pair

/-!
# The translated first-pair calculation

The arrays below cache exact AES difference counts and support masks.
The exceptional coordinate pairs are data: their completeness is verified
against all nonzero endpoint differences and all 256 translations.
-/

namespace PairwiseIndependence

/-- Cache the affine output-index permutation once for the finite search. -/
def keliherSuiAffineIndexTable : Array Nat :=
  Array.ofFn (fun t : Fin 256 => (aesInverseAffineDifferenceIndex t).val)

theorem keliherSuiAffineIndexTable_get (t : Fin 256) :
    keliherSuiAffineIndexTable[t.val]! =
      (aesInverseAffineDifferenceIndex t).val := by
  simp [keliherSuiAffineIndexTable]

def keliherSuiXor (x y : Fin 256) : Fin 256 :=
  ⟨(x.val ^^^ y.val) % 256, Nat.mod_lt _ (by omega)⟩

theorem keliherSuiXor_byte : ∀ x y : Fin 256,
    aesByteFinEquiv (keliherSuiXor x y) =
      aesByteFinEquiv x + aesByteFinEquiv y := by
  native_decide

theorem keliherSuiXor_cancel : ∀ x y : Fin 256,
    keliherSuiXor (keliherSuiXor x y) y = x := by
  native_decide

def keliherSuiCounts : Array (Array Nat) :=
  let D := aesInverseDifferenceCountTable
  let I := keliherSuiAffineIndexTable
  Array.ofFn (fun a : Fin 256 =>
    Array.ofFn (fun b : Fin 256 => (D[a.val]!)[I[b.val]!]!))

theorem keliherSuiCounts_get (a b : Fin 256) :
    (keliherSuiCounts[a.val]!)[b.val]! =
      aesSboxDifferenceCountFin a b := by
  simp [keliherSuiCounts, keliherSuiAffineIndexTable_get,
    aesSboxDifferenceCountFin_index]

def keliherSuiRowSpecials (C : Array (Array Nat)) : Array (Fin 256) :=
  Array.ofFn (fun a : Fin 256 =>
    ⟨(∑ t : Fin 256, if (C[a.val]!)[t.val]! = 4 then t.val else 0) % 256,
      Nat.mod_lt _ (by omega)⟩)

def keliherSuiColumnSpecials (C : Array (Array Nat)) : Array (Fin 256) :=
  Array.ofFn (fun b : Fin 256 =>
    ⟨(∑ t : Fin 256, if (C[t.val]!)[b.val]! = 4 then t.val else 0) % 256,
      Nat.mod_lt _ (by omega)⟩)

def keliherSuiExceptionalPairs : List (Fin 256 × Fin 256) :=
  [(3, 228), (5, 249), (6, 220), (9, 11), (14, 239), (21, 10),
   (28, 245), (29, 218), (33, 109), (35, 143), (38, 139), (38, 172),
   (40, 150), (41, 253), (49, 113), (53, 68), (62, 224), (63, 250),
   (78, 188), (86, 112), (93, 54), (93, 234), (101, 115), (105, 73),
   (106, 37), (110, 160), (112, 47), (114, 234), (116, 105), (120, 106),
   (136, 222), (138, 206), (143, 29), (144, 113), (145, 223), (147, 254),
   (149, 173), (150, 34), (160, 178), (163, 153), (165, 168), (167, 107),
   (169, 178), (170, 238), (174, 203), (175, 19), (178, 129), (182, 15),
   (188, 238), (193, 130), (201, 206), (206, 191), (211, 181), (213, 154),
   (216, 181), (217, 53), (223, 111), (224, 49), (229, 28), (236, 250),
   (240, 118), (240, 139), (247, 53)]

def keliherSuiPackedRows (C : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (fun a : Fin 256 =>
    keliherSuiPackedProfile (fun t => (C[a.val]!)[t.val]!))

def keliherSuiPackedTranslatedColumns (C : Array (Array Nat)) :
    Array (Array (Array Nat)) :=
  Array.ofFn (fun o : Fin 256 => Array.ofFn (fun b : Fin 256 =>
    keliherSuiPackedProfile (fun t =>
      (C[(keliherSuiXor t o).val]!)[b.val]!)))

def keliherSuiTranslatedPairSum
    (C : Array (Array Nat)) (bits : Array Nat)
    (rows : Array (Array Nat)) (cols : Array (Array (Array Nat)))
    (rs cs : Array (Fin 256)) (a b o : Fin 256) : Nat :=
  let sp := rs[a.val]!
  let sq := keliherSuiXor cs[b.val]! o
  4 * (keliherSuiPackedIntersection bits rows[a.val]! (cols[o.val]!)[b.val]! +
    (if (C[(keliherSuiXor sp o).val]!)[b.val]! = 0 then 0 else 1) +
    (if (C[a.val]!)[sq.val]! = 0 then 0 else 1) +
    (if sp = sq then 1 else 0))

theorem keliherSuiSpecials_spec :
    let C := keliherSuiCounts
    let rs := keliherSuiRowSpecials C
    let cs := keliherSuiColumnSpecials C
    ∀ a t : Fin 256, a ≠ 0 →
      ((C[a.val]!)[t.val]! = 4 ↔ t = rs[a.val]!) ∧
      ((C[t.val]!)[a.val]! = 4 ↔ t = cs[a.val]!) := by
  native_decide

/-- The verifier is parameterized before specializing to the large arrays.
This keeps elaboration from repeatedly unfolding the cached data. -/
def KeliherSuiTranslatedPairCheck
    (C : Array (Array Nat)) (bits : Array Nat)
    (rows : Array (Array Nat)) (cols : Array (Array (Array Nat)))
    (rs cs : Array (Fin 256)) : Prop :=
  ∀ a b o : Fin 256, a ≠ 0 → b ≠ 0 →
    let sp := rs[a.val]!
    let sq := keliherSuiXor cs[b.val]! o
    8 * (keliherSuiTranslatedPairSum C bits rows cols rs cs a b o +
      7 * (if sp = sq then 16 else 8)) ≤ 3392 ∨
    (sp = sq ∧ (sp, cs[b.val]!) ∈ keliherSuiExceptionalPairs)

/-- A boolean traversal shares each translated column across the 256
row checks. The theorem below identifies it with the quantified certificate. -/
def keliherSuiTranslatedPairsCheckBool
    (C : Array (Array Nat)) (bits : Array Nat)
    (rows : Array (Array Nat)) (cols : Array (Array (Array Nat)))
    (rs cs : Array (Fin 256)) : Bool :=
  (List.finRange 256).all fun o =>
    let columns := cols[o.val]!
    (List.finRange 256).all fun b =>
      if b = 0 then true else
      let column := columns[b.val]!
      let sq := keliherSuiXor cs[b.val]! o
      (List.finRange 256).all fun a =>
        if a = 0 then true else
        let sp := rs[a.val]!
        let total := 4 * (keliherSuiPackedIntersection bits rows[a.val]! column +
          (if (C[(keliherSuiXor sp o).val]!)[b.val]! = 0 then 0 else 1) +
          (if (C[a.val]!)[sq.val]! = 0 then 0 else 1) +
          (if sp = sq then 1 else 0))
        decide (8 * (total + 7 * (if sp = sq then 16 else 8)) ≤ 3392) ||
          (decide (sp = sq) && decide ((sp, cs[b.val]!) ∈ keliherSuiExceptionalPairs))

theorem keliherSuiTranslatedPairsCheckBool_iff
    (C : Array (Array Nat)) (bits : Array Nat)
    (rows : Array (Array Nat)) (cols : Array (Array (Array Nat)))
    (rs cs : Array (Fin 256)) :
    keliherSuiTranslatedPairsCheckBool C bits rows cols rs cs = true ↔
      KeliherSuiTranslatedPairCheck C bits rows cols rs cs := by
  simp only [keliherSuiTranslatedPairsCheckBool, List.all_eq_true,
    List.mem_finRange, forall_const, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, ite_eq_left_iff]
  unfold KeliherSuiTranslatedPairCheck keliherSuiTranslatedPairSum
  aesop

/-- Exhaustive verification of the 63 exceptional translated pairs. -/
theorem keliherSuiTranslatedPairs_certificate :
    KeliherSuiTranslatedPairCheck keliherSuiCounts keliherSuiBitCounts
      (keliherSuiPackedRows keliherSuiCounts)
      (keliherSuiPackedTranslatedColumns keliherSuiCounts)
      (keliherSuiRowSpecials keliherSuiCounts)
      (keliherSuiColumnSpecials keliherSuiCounts) := by
  apply (keliherSuiTranslatedPairsCheckBool_iff _ _ _ _ _ _).1
  native_decide

end PairwiseIndependence

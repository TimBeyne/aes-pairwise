import PairwiseIndependence.KeliherSui.AffinePairs

namespace PairwiseIndependence

def keliherSuiRowSpecial (a : Fin 256) : Fin 256 :=
  (keliherSuiRowSpecials keliherSuiCounts)[a.val]!

def keliherSuiColumnSpecial (b : Fin 256) : Fin 256 :=
  (keliherSuiColumnSpecials keliherSuiCounts)[b.val]!

theorem keliherSuiRowSpecial_spec (a t : Fin 256) (ha : a ≠ 0) :
    aesSboxDifferenceCountFin a t = 4 ↔ t = keliherSuiRowSpecial a := by
  simpa only [keliherSuiCounts_get, keliherSuiRowSpecial] using
    (keliherSuiSpecials_spec a t ha).1

theorem keliherSuiColumnSpecial_spec (b t : Fin 256) (hb : b ≠ 0) :
    aesSboxDifferenceCountFin t b = 4 ↔ t = keliherSuiColumnSpecial b := by
  simpa only [keliherSuiCounts_get, keliherSuiColumnSpecial] using
    (keliherSuiSpecials_spec b t hb).2

theorem keliherSuiXor_eq_iff (t o s : Fin 256) :
    keliherSuiXor t o = s ↔ t = keliherSuiXor s o := by
  constructor
  · intro h
    rw [← h, keliherSuiXor_cancel]
  · intro h
    rw [h, keliherSuiXor_cancel]

theorem keliherSuiTranslatedPairSum_eq
    (a b o : Fin 256) (ha : a ≠ 0) (hb : b ≠ 0) :
    keliherSuiTranslatedPairSum keliherSuiCounts keliherSuiBitCounts
      (keliherSuiPackedRows keliherSuiCounts)
      (keliherSuiPackedTranslatedColumns keliherSuiCounts)
      (keliherSuiRowSpecials keliherSuiCounts)
      (keliherSuiColumnSpecials keliherSuiCounts) a b o =
      ∑ t : Fin 256, aesSboxDifferenceCountFin a t *
        aesSboxDifferenceCountFin (keliherSuiXor t o) b := by
  have h := keliherSui_pair_sum_eq_support_formula
    (fun t => aesSboxDifferenceCountFin a t)
    (fun t => aesSboxDifferenceCountFin (keliherSuiXor t o) b)
    (keliherSuiRowSpecial a) (keliherSuiXor (keliherSuiColumnSpecial b) o)
    (aesSboxDifferenceCountFin_row_three_values a ha)
    (fun t => aesSboxDifferenceCountFin_column_three_values b hb _)
    (fun t => keliherSuiRowSpecial_spec a t ha)
    (fun t => (keliherSuiColumnSpecial_spec b _ hb).trans
      (keliherSuiXor_eq_iff t o _))
  rw [h]
  unfold keliherSuiTranslatedPairSum keliherSuiPackedRows
    keliherSuiPackedTranslatedColumns
  simp only [keliherSui_ofFn_get]
  rw [keliherSuiPackedIntersection_eq]
  simp only [keliherSuiCounts_get, keliherSuiCountSupport,
    keliherSuiRowSpecial, keliherSuiColumnSpecial]

/-- Every translated AES row/column pair either prunes three arbitrary
remaining profiles or has coincident count-four positions belonging to
the verified list of 63 exceptional coordinate pairs. -/
theorem keliherSui_translated_pair_prunes_or_exception
    (a b o : Fin 256) (ha : a ≠ 0) (hb : b ≠ 0) :
    8 * ((∑ t : Fin 256, aesSboxDifferenceCountFin a t *
      aesSboxDifferenceCountFin (keliherSuiXor t o) b) +
      7 * (if keliherSuiRowSpecial a =
        keliherSuiXor (keliherSuiColumnSpecial b) o then 16 else 8)) ≤ 3392 ∨
    (keliherSuiRowSpecial a =
      keliherSuiXor (keliherSuiColumnSpecial b) o ∧
      (keliherSuiRowSpecial a, keliherSuiColumnSpecial b) ∈
        keliherSuiExceptionalPairs) := by
  have h := keliherSuiTranslatedPairs_certificate a b o ha hb
  simpa only [keliherSuiTranslatedPairSum_eq a b o ha hb,
    keliherSuiRowSpecial, keliherSuiColumnSpecial] using h

end PairwiseIndependence

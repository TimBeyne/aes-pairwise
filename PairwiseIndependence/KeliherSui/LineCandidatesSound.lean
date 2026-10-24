import PairwiseIndependence.KeliherSui.LineProfiles

namespace PairwiseIndependence

theorem keliherSuiLineInput_first : ∀ s : Fin 56,
    keliherSuiLineInput s 0 = true ∧ keliherSuiLineInput s 1 = false := by
  native_decide

theorem keliherSuiLineCandidate_mem (s : Fin 56) (z : Fin 5 → Fin 256)
    (hbad : ∀ i j : Fin 5, keliherSuiLineInput s i = true →
      keliherSuiLineInput s j = false →
      (z i, keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
        (z j)) ∈ keliherSuiExceptionalPairs) (i : Fin 5) :
    z i ∈ keliherSuiLineOptions s i (z 0) (z 1) := by
  unfold keliherSuiLineOptions keliherSuiLineOptionsWith
  split_ifs with hi
  · refine List.mem_map.mpr ⟨(z i, keliherSuiMultiply
      (keliherSuiInverse (keliherSuiLineRatio s i 1)) (z 1)), ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨hbad i 1 hi (keliherSuiLineInput_first s).2, ?_⟩
    simpa only [decide_eq_true_eq] using
      (keliherSuiMultiplication_inverse _ (z 1)
        (keliherSuiLineRatio_certificate s i 1).1).2
  · have hi' : keliherSuiLineInput s i = false := Bool.eq_false_iff.mpr hi
    refine List.mem_map.mpr ⟨(z 0, keliherSuiMultiply
      (keliherSuiInverse (keliherSuiLineRatio s 0 i)) (z i)), ?_, ?_⟩
    · exact List.mem_filter.mpr
        ⟨hbad 0 i (keliherSuiLineInput_first s).1 hi', by simp⟩
    · exact (keliherSuiMultiplication_inverse _ (z i)
        (keliherSuiLineRatio_certificate s 0 i).1).2

/-- Completeness of the short candidate lists. Only mixed pairs involving
the first input or the first output are needed to enumerate every
configuration surviving all pair tests. -/
theorem keliherSuiLineCandidates_bound (s : Fin 56) (z : Fin 5 → Fin 256)
    (hcompat : keliherSuiLineCompatible s z)
    (hbad : ∀ i j : Fin 5, keliherSuiLineInput s i = true →
      keliherSuiLineInput s j = false →
      (z i, keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
        (z j)) ∈ keliherSuiExceptionalPairs) :
    keliherSuiLineFiveSum keliherSuiCounts keliherSuiMultiplication
      keliherSuiRowEndpoints keliherSuiColumnEndpoints s z ≤ 3392 := by
  have hroot := hbad 0 1 (keliherSuiLineInput_first s).1 (keliherSuiLineInput_first s).2
  have h := keliherSuiLineCandidates_certificate s _ hroot
  have hinv : keliherSuiMultiply (keliherSuiLineRatio s 0 1)
      (keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s 0 1)) (z 1)) = z 1 :=
    (keliherSuiMultiplication_inverse _ (z 1)
      (keliherSuiLineRatio_certificate s 0 1).1).2
  let y := keliherSuiMultiply (keliherSuiLineRatio s 0 1)
    (keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s 0 1)) (z 1))
  change ∀ z₂ ∈ keliherSuiLineOptions s 2 (z 0) y,
    ∀ z₃ ∈ keliherSuiLineOptions s 3 (z 0) y,
    ∀ z₄ ∈ keliherSuiLineOptions s 4 (z 0) y,
    keliherSuiLineCompatibleFast (keliherSuiBasisTable keliherSuiMultiplication)
      s ![z 0, y, z₂, z₃, z₄] →
    keliherSuiLineFiveSum keliherSuiCounts keliherSuiMultiplication
      keliherSuiRowEndpoints keliherSuiColumnEndpoints s ![z 0, y, z₂, z₃, z₄] ≤ 3392 at h
  change y = z 1 at hinv
  rw [hinv] at h
  have hv : ![z 0, z 1, z 2, z 3, z 4] = z := by
    funext i
    fin_cases i <;> rfl
  have h' := h (z 2) (keliherSuiLineCandidate_mem s z hbad 2)
    (z 3) (keliherSuiLineCandidate_mem s z hbad 3)
    (z 4) (keliherSuiLineCandidate_mem s z hbad 4)
  rw [hv] at h'
  exact h' ((keliherSuiLineCompatibleFast_iff s z).2 hcompat)

end PairwiseIndependence

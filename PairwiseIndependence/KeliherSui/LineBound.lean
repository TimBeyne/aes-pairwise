import PairwiseIndependence.KeliherSui.LineCandidatesSound

namespace PairwiseIndependence

theorem keliherSuiLineCoordinate_shift (s : Fin 56) (base : State AesByte 4)
    (i : Fin 5) (t r : Fin 256) :
    keliherSuiLineCoordinate s base i (keliherSuiXor t r) =
      keliherSuiXor (keliherSuiLineCoordinate s base i r)
        (keliherSuiMultiply (keliherSuiLineCoefficient s i) t) := by
  rw [keliherSuiLineCoordinate_apply, keliherSuiLineCoordinate_apply,
    keliherSuiMultiply_xor]
  apply aesByteFinEquiv.injective
  simp only [keliherSuiXor_byte]
  abel

/-- The complete bound for all affine five-lists of the concrete
MixColumns graph, with arbitrary nonzero endpoint differences. -/
theorem keliherSuiLine_bound (s : Fin 56) (base : State AesByte 4)
    (endpoint : Fin 5 → Fin 256) (he : ∀ i, endpoint i ≠ 0) :
    (∑ t : Fin 256, ∏ i : Fin 5, keliherSuiLineProfile s base endpoint i t) ≤ 3392 := by
  classical
  by_contra hlarge
  let special := keliherSuiLineSpecial s base endpoint
  have hbad (i j : Fin 5) (hi : keliherSuiLineInput s i = true)
      (hj : keliherSuiLineInput s j = false) :
      special i = special j ∧
      (keliherSuiRowSpecial (endpoint i),
        keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
          (keliherSuiColumnSpecial (endpoint j))) ∈ keliherSuiExceptionalPairs := by
    rcases keliherSuiLinePair_dichotomy s base endpoint he i j hi hj with h | h
    · have hij : i ≠ j := fun h =>
        Bool.noConfusion (hi.symm.trans ((congrArg (keliherSuiLineInput s) h).trans hj))
      exact False.elim (hlarge (keliherSui_five_product_le_of_pair
        (keliherSuiLineProfile s base endpoint) special
        (keliherSuiLineProfile_bound s base endpoint he) i j hij h))
    · exact h
  have h01 := (hbad 0 1 (keliherSuiLineInput_first s).1
    (keliherSuiLineInput_first s).2).1
  have hall (i : Fin 5) : special i = special 0 := by
    cases hi : keliherSuiLineInput s i with
    | false => exact (hbad 0 i (keliherSuiLineInput_first s).1 hi).1.symm
    | true => exact (hbad i 1 hi (keliherSuiLineInput_first s).2).1.trans h01.symm
  let z : Fin 5 → Fin 256 := fun i => keliherSuiLineCoordinate s base i (special 0)
  have hz (i : Fin 5) : z i =
      if keliherSuiLineInput s i then keliherSuiRowSpecial (endpoint i)
      else keliherSuiColumnSpecial (endpoint i) := by
    change keliherSuiLineCoordinate s base i (special 0) = _
    rw [← hall i]
    exact (keliherSuiLineCoordinate s base i).apply_symm_apply _
  have hbadz (i j : Fin 5) (hi : keliherSuiLineInput s i = true)
      (hj : keliherSuiLineInput s j = false) :
      (z i, keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
        (z j)) ∈ keliherSuiExceptionalPairs := by
    simpa only [hz, hi, hj, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
      using (hbad i j hi hj).2
  let x := base + keliherSuiLineDirection s (aesByteFinEquiv (special 0))
  have hzbyte (i : Fin 5) : aesByteFinEquiv (z i) =
      mdsGraphCoordinate aesMixColumnEquiv x (keliherSuiLineFree s i) :=
    keliherSuiLineCoordinate_byte s base i (special 0)
  have hcompat : keliherSuiLineCompatible s z := by
    unfold keliherSuiLineCompatible
    simp_rw [hzbyte]
    rw [keliherSuiLine_reconstruct]
  have hbound := keliherSuiLineCandidates_bound s z hcompat hbadz
  have hsum :
      keliherSuiLineFiveSum keliherSuiCounts keliherSuiMultiplication
        keliherSuiRowEndpoints keliherSuiColumnEndpoints s z =
      ∑ t : Fin 256, ∏ i : Fin 5, keliherSuiLineProfile s base endpoint i t := by
    unfold keliherSuiLineFiveSum
    apply Fintype.sum_equiv (keliherSuiXorEquiv (special 0))
    intro t
    apply Finset.prod_congr rfl
    intro i _
    unfold keliherSuiLineProfile
    have hshift : keliherSuiLineCoordinate s base i
        (keliherSuiXorEquiv (special 0) t) =
        keliherSuiXor (z i) (keliherSuiMultiply (keliherSuiLineCoefficient s i) t) :=
      keliherSuiLineCoordinate_shift s base i t (special 0)
    rw [hshift]
    cases hi : keliherSuiLineInput s i with
    | true =>
      have hzi : z i = keliherSuiRowSpecial (endpoint i) := by simpa [hi] using hz i
      have hre : keliherSuiRowEndpoints[(keliherSuiRowSpecial (endpoint i)).val]! =
          endpoint i := (keliherSuiEndpoints_spec (endpoint i) (he i)).1
      simp only [↓reduceIte, hzi, hre, keliherSuiCounts_get, keliherSuiMultiply]
    | false =>
      have hzi : z i = keliherSuiColumnSpecial (endpoint i) := by simpa [hi] using hz i
      have hce : keliherSuiColumnEndpoints[(keliherSuiColumnSpecial (endpoint i)).val]! =
          endpoint i := (keliherSuiEndpoints_spec (endpoint i) (he i)).2
      simp only [Bool.false_eq_true, ↓reduceIte, hzi, hce, keliherSuiCounts_get,
        keliherSuiMultiply]
  exact hlarge (hsum ▸ hbound)

end PairwiseIndependence

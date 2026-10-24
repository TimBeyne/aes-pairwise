import PairwiseIndependence.KeliherSui.LineData

namespace PairwiseIndependence

theorem keliherSuiLine_free_not_fixed (s : Fin 56) (i : Fin 5) :
    keliherSuiLineFree s i ∉ keliherSuiLineFixed s := by
  have h : keliherSuiLineFree s i ∈
      Finset.univ.image (keliherSuiLineFree s) := Finset.mem_image.mpr
    ⟨i, Finset.mem_univ _, rfl⟩
  rw [(keliherSuiLine_indices s).2.2.1] at h
  exact (Finset.mem_sdiff.mp h).2

theorem keliherSuiLineDirection_fixed (s : Fin 56) (t : AesByte)
    (j : KeliherSuiGraphIndex) (hj : j ∈ keliherSuiLineFixed s) :
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s t) j = 0 := by
  have h := (keliherSuiLineDirection_certificate s (aesByteFinEquiv.symm t)).1 j hj
  simpa only [keliherSuiDirectionTable_get, Equiv.apply_symm_apply] using h

theorem keliherSuiLineDirection_free (s : Fin 56) (t : AesByte) (i : Fin 5) :
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s t)
      (keliherSuiLineFree s i) =
      aesByteMul t (aesByteFinEquiv (keliherSuiLineCoefficient s i)) := by
  have h := (keliherSuiLineDirection_certificate s (aesByteFinEquiv.symm t)).2 i
  simp only [keliherSuiDirectionTable_get, Equiv.apply_symm_apply] at h
  change mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s t)
    (keliherSuiLineFree s i) = aesByteFinEquiv
      (keliherSuiMultiply (keliherSuiLineCoefficient s i) (aesByteFinEquiv.symm t)) at h
  rw [keliherSuiMultiply_byte, Equiv.apply_symm_apply] at h
  exact h

theorem keliherSuiLineDirection_first (s : Fin 56) (t : AesByte) :
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s t)
      (keliherSuiLineFree s 0) = t := by
  rw [keliherSuiLineDirection_free, (keliherSuiLine_indices s).2.2.2.2.2.2]
  have h : ∀ t : Fin 256,
      aesByteMul (aesByteFinEquiv t) (aesByteFinEquiv (1 : Fin 256)) =
        aesByteFinEquiv t := by native_decide
  simpa using h (aesByteFinEquiv.symm t)

theorem keliherSuiByte_self_add (x : AesByte) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

theorem keliherSuiLineBasis_free (s : Fin 56) (j k : Fin 4) (t : AesByte) :
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineBasis s j t)
      (keliherSuiLineFree s k.castSucc) = if k = j then t else 0 := by
  have h := keliherSuiLineBasis_certificate s j k (aesByteFinEquiv.symm t)
  simpa only [keliherSuiBasisTable_get, Equiv.apply_symm_apply] using h

theorem keliherSuiLineReconstruct_free (s : Fin 56) (v : Fin 4 → AesByte)
    (k : Fin 4) :
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineReconstruct s v)
      (keliherSuiLineFree s k.castSucc) = v k := by
  change keliherSuiGraphCoordinateHom _ (∑ j : Fin 4, _) = _
  rw [map_sum]
  change (∑ j : Fin 4, mdsGraphCoordinate aesMixColumnEquiv
    (keliherSuiLineBasis s j (v j)) (keliherSuiLineFree s k.castSucc)) = _
  simp [keliherSuiLineBasis_free]

theorem keliherSuiLine_reconstruct (s : Fin 56) (x : State AesByte 4) :
    keliherSuiLineReconstruct s (fun j => mdsGraphCoordinate aesMixColumnEquiv x
      (keliherSuiLineFree s j.castSucc)) = x := by
  let S := (Finset.univ : Finset (Fin 4)).image
    (fun j => keliherSuiLineFree s j.castSucc)
  have hi : Function.Injective (fun j : Fin 4 => keliherSuiLineFree s j.castSucc) :=
    (keliherSuiLine_indices s).2.1.comp (Fin.castSucc_injective 4)
  have hc : S.card = 4 := by simp [S, Finset.card_image_of_injective _ hi]
  apply aesMixColumn_isMDS.graphProjection_injective aesMixColumnEquiv S (by omega)
  funext j
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp j.2
  change mdsGraphCoordinate aesMixColumnEquiv _ j.1 =
    mdsGraphCoordinate aesMixColumnEquiv x j.1
  rw [← hk, keliherSuiLineReconstruct_free]

/-- Translate the certified one-byte kernel direction through any point of
a fixed-coordinate fiber. MDS injectivity on four coordinates proves that
this enumerates the entire fiber exactly once. -/
def keliherSuiLineFiberEquiv (s : Fin 56)
    (v : keliherSuiLineFixed s → AesByte)
    (base : State AesByte 4)
    (hbase : mdsGraphProjection aesMixColumnEquiv (keliherSuiLineFixed s) base = v) :
    AesByte ≃ {x : State AesByte 4 //
      mdsGraphProjection aesMixColumnEquiv (keliherSuiLineFixed s) x = v} where
  toFun t := ⟨base + keliherSuiLineDirection s t, by
    rw [map_add, hbase]
    have hzero : mdsGraphProjection aesMixColumnEquiv
        (keliherSuiLineFixed s) (keliherSuiLineDirection s t) = 0 := by
      funext j
      exact keliherSuiLineDirection_fixed s t j.1 j.2
    rw [hzero, add_zero]⟩
  invFun x := mdsGraphCoordinate aesMixColumnEquiv x.1 (keliherSuiLineFree s 0) +
    mdsGraphCoordinate aesMixColumnEquiv base (keliherSuiLineFree s 0)
  left_inv t := by
    change keliherSuiGraphCoordinateHom _ (base + keliherSuiLineDirection s t) + _ = _
    rw [map_add]
    change (mdsGraphCoordinate aesMixColumnEquiv base (keliherSuiLineFree s 0) +
      mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s t)
      (keliherSuiLineFree s 0)) + _ = _
    rw [keliherSuiLineDirection_first]
    rw [add_right_comm, keliherSuiByte_self_add, zero_add]
  right_inv x := by
    apply Subtype.ext
    let S := insert (keliherSuiLineFree s 0) (keliherSuiLineFixed s)
    have hc : S.card = 4 := by
      simp [S, keliherSuiLine_free_not_fixed, (keliherSuiLine_indices s).1]
    apply aesMixColumn_isMDS.graphProjection_injective aesMixColumnEquiv S (by omega)
    funext j
    rcases Finset.mem_insert.mp j.2 with hj | hj
    · change keliherSuiGraphCoordinateHom j.1 (_ + _) = _
      rw [map_add]
      change mdsGraphCoordinate aesMixColumnEquiv base j.1 +
        mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s _) j.1 =
        mdsGraphCoordinate aesMixColumnEquiv x.1 j.1
      rw [hj, keliherSuiLineDirection_first, add_left_comm,
        keliherSuiByte_self_add, add_zero]
    · change keliherSuiGraphCoordinateHom j.1 (_ + _) = _
      rw [map_add]
      change mdsGraphCoordinate aesMixColumnEquiv base j.1 +
        mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s _) j.1 =
        mdsGraphCoordinate aesMixColumnEquiv x.1 j.1
      rw [keliherSuiLineDirection_fixed s _ j.1 hj, add_zero]
      exact (congrFun hbase ⟨j.1, hj⟩).trans (congrFun x.2 ⟨j.1, hj⟩).symm

end PairwiseIndependence

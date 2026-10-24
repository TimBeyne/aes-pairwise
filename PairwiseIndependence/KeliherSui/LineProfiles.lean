import PairwiseIndependence.KeliherSui.LineCandidates
import PairwiseIndependence.KeliherSui.ScaledPairs

namespace PairwiseIndependence

def KeliherSuiLineRatioCheck (M : Array (Array (Fin 256))) : Prop :=
  ∀ (s : Fin 56) (i j : Fin 5), keliherSuiLineRatioWith M s i j ≠ 0 ∧
    ∀ t : Fin 256,
      (M[(keliherSuiLineRatioWith M s i j).val]!)[
        ((M[(keliherSuiLineCoefficient s i).val]!)[t.val]!).val]! =
      (M[(keliherSuiLineCoefficient s j).val]!)[t.val]!

instance (M : Array (Array (Fin 256))) : Decidable (KeliherSuiLineRatioCheck M) :=
  inferInstanceAs (Decidable (∀ (s : Fin 56) (i j : Fin 5),
    keliherSuiLineRatioWith M s i j ≠ 0 ∧ ∀ t : Fin 256,
      (M[(keliherSuiLineRatioWith M s i j).val]!)[
        ((M[(keliherSuiLineCoefficient s i).val]!)[t.val]!).val]! =
      (M[(keliherSuiLineCoefficient s j).val]!)[t.val]!))

theorem keliherSuiLineRatio_certificate :
    KeliherSuiLineRatioCheck keliherSuiMultiplication := by native_decide

def keliherSuiLineCoordinate (s : Fin 56) (base : State AesByte 4) (i : Fin 5) :
    Fin 256 ≃ Fin 256 :=
  (keliherSuiMultiplyEquiv (keliherSuiLineCoefficient s i)
    ((keliherSuiLine_indices s).2.2.2.2.2.1 i)).trans
    (keliherSuiXorEquiv (aesByteFinEquiv.symm
      (mdsGraphCoordinate aesMixColumnEquiv base (keliherSuiLineFree s i))))

theorem keliherSuiLineCoordinate_apply (s : Fin 56) (base : State AesByte 4)
    (i : Fin 5) (t : Fin 256) :
    keliherSuiLineCoordinate s base i t =
      keliherSuiXor (keliherSuiMultiply (keliherSuiLineCoefficient s i) t)
        (aesByteFinEquiv.symm
          (mdsGraphCoordinate aesMixColumnEquiv base (keliherSuiLineFree s i))) := rfl

theorem keliherSuiLineCoordinate_byte (s : Fin 56) (base : State AesByte 4)
    (i : Fin 5) (t : Fin 256) :
    aesByteFinEquiv (keliherSuiLineCoordinate s base i t) =
      mdsGraphCoordinate aesMixColumnEquiv
        (base + keliherSuiLineDirection s (aesByteFinEquiv t))
        (keliherSuiLineFree s i) := by
  rw [keliherSuiLineCoordinate_apply, keliherSuiXor_byte,
    keliherSuiMultiply_byte, Equiv.apply_symm_apply]
  have hadd := (keliherSuiGraphCoordinateHom (keliherSuiLineFree s i)).map_add
    base (keliherSuiLineDirection s (aesByteFinEquiv t))
  change mdsGraphCoordinate aesMixColumnEquiv
    (base + keliherSuiLineDirection s (aesByteFinEquiv t)) (keliherSuiLineFree s i) =
    mdsGraphCoordinate aesMixColumnEquiv base (keliherSuiLineFree s i) +
    mdsGraphCoordinate aesMixColumnEquiv (keliherSuiLineDirection s (aesByteFinEquiv t))
      (keliherSuiLineFree s i) at hadd
  rw [hadd, keliherSuiLineDirection_free, add_comm]

def keliherSuiLinePairOffset (s : Fin 56) (base : State AesByte 4) (i j : Fin 5) :
    Fin 256 :=
  keliherSuiXor
    (aesByteFinEquiv.symm (mdsGraphCoordinate aesMixColumnEquiv base
      (keliherSuiLineFree s i)))
    (keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
      (aesByteFinEquiv.symm (mdsGraphCoordinate aesMixColumnEquiv base
        (keliherSuiLineFree s j))))

theorem keliherSuiLineCoordinate_ratio (s : Fin 56) (base : State AesByte 4)
    (i j : Fin 5) (t : Fin 256) :
    keliherSuiLineCoordinate s base j t =
      keliherSuiMultiply (keliherSuiLineRatio s i j)
        (keliherSuiXor (keliherSuiLineCoordinate s base i t)
          (keliherSuiLinePairOffset s base i j)) := by
  rw [keliherSuiLineCoordinate_apply, keliherSuiLineCoordinate_apply]
  unfold keliherSuiLinePairOffset
  rw [keliherSuiXor_join, keliherSuiMultiply_xor]
  rw [show keliherSuiMultiply (keliherSuiLineRatio s i j)
    (keliherSuiMultiply (keliherSuiLineCoefficient s i) t) =
      keliherSuiMultiply (keliherSuiLineCoefficient s j) t from
        (keliherSuiLineRatio_certificate s i j).2 t]
  rw [show ∀ v, keliherSuiMultiply (keliherSuiLineRatio s i j)
    (keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j)) v) = v from
      fun v => (keliherSuiMultiplication_inverse _ v
        (keliherSuiLineRatio_certificate s i j).1).2]

def keliherSuiLineProfile (s : Fin 56) (base : State AesByte 4)
    (endpoint : Fin 5 → Fin 256) (i : Fin 5) (t : Fin 256) : Nat :=
  if keliherSuiLineInput s i then
    aesSboxDifferenceCountFin (endpoint i) (keliherSuiLineCoordinate s base i t)
  else aesSboxDifferenceCountFin (keliherSuiLineCoordinate s base i t) (endpoint i)

def keliherSuiLineSpecial (s : Fin 56) (base : State AesByte 4)
    (endpoint : Fin 5 → Fin 256) (i : Fin 5) : Fin 256 :=
  (keliherSuiLineCoordinate s base i).symm
    (if keliherSuiLineInput s i then keliherSuiRowSpecial (endpoint i)
      else keliherSuiColumnSpecial (endpoint i))

theorem keliherSuiLineProfile_bound (s : Fin 56) (base : State AesByte 4)
    (endpoint : Fin 5 → Fin 256) (he : ∀ i, endpoint i ≠ 0) (i : Fin 5) (t : Fin 256) :
    keliherSuiLineProfile s base endpoint i t ≤
      2 * (if t = keliherSuiLineSpecial s base endpoint i then 2 else 1) := by
  apply keliherSui_profile_bound
  · intro u
    unfold keliherSuiLineProfile
    split_ifs
    · exact aesSboxDifferenceCountFin_row_three_values _ (he i) _
    · exact aesSboxDifferenceCountFin_column_three_values _ (he i) _
  · intro u
    unfold keliherSuiLineProfile keliherSuiLineSpecial
    split_ifs
    · rw [keliherSuiRowSpecial_spec _ _ (he i)]
      exact (keliherSuiLineCoordinate s base i).apply_eq_iff_eq_symm_apply
    · rw [keliherSuiColumnSpecial_spec _ _ (he i)]
      exact (keliherSuiLineCoordinate s base i).apply_eq_iff_eq_symm_apply

theorem keliherSuiLinePair_dichotomy (s : Fin 56) (base : State AesByte 4)
    (endpoint : Fin 5 → Fin 256) (he : ∀ i, endpoint i ≠ 0)
    (i j : Fin 5) (hi : keliherSuiLineInput s i = true)
    (hj : keliherSuiLineInput s j = false) :
    8 * ((∑ t : Fin 256, keliherSuiLineProfile s base endpoint i t *
      keliherSuiLineProfile s base endpoint j t) +
      7 * (if keliherSuiLineSpecial s base endpoint i =
        keliherSuiLineSpecial s base endpoint j then 16 else 8)) ≤ 3392 ∨
    (keliherSuiLineSpecial s base endpoint i = keliherSuiLineSpecial s base endpoint j ∧
      (keliherSuiRowSpecial (endpoint i),
        keliherSuiMultiply (keliherSuiInverse (keliherSuiLineRatio s i j))
          (keliherSuiColumnSpecial (endpoint j))) ∈ keliherSuiExceptionalPairs) := by
  have h := keliherSui_affine_pair_prunes_or_exception
    (endpoint i) (endpoint j) (keliherSuiLineRatio s i j)
    (keliherSuiLinePairOffset s base i j) (he i) (he j)
    (keliherSuiLineRatio_certificate s i j).1
    (keliherSuiLineCoordinate s base i) (keliherSuiLineCoordinate s base j)
    (keliherSuiLineCoordinate_ratio s base i j)
  simpa only [keliherSuiLineProfile, keliherSuiLineSpecial, hi, hj,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte] using h

end PairwiseIndependence

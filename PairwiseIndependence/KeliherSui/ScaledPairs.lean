import PairwiseIndependence.KeliherSui.FivePruning

namespace PairwiseIndependence

theorem keliherSuiColumnSpecial_scaled (c b : Fin 256)
    (hc : c ≠ 0) (hb : b ≠ 0) :
    keliherSuiColumnSpecial (keliherSuiScaleOutput c b) =
      keliherSuiMultiply (keliherSuiInverse c) (keliherSuiColumnSpecial b) := by
  have h4 := (keliherSuiColumnSpecial_spec b (keliherSuiColumnSpecial b) hb).2 rfl
  have hinv := (keliherSuiMultiplication_inverse c (keliherSuiColumnSpecial b) hc).2
  have hcount := keliherSui_scaled_count c
    (keliherSuiMultiply (keliherSuiInverse c) (keliherSuiColumnSpecial b)) b hc
  rw [show keliherSuiMultiply c
    (keliherSuiMultiply (keliherSuiInverse c) (keliherSuiColumnSpecial b)) =
      keliherSuiColumnSpecial b from hinv, h4] at hcount
  exact ((keliherSuiColumnSpecial_spec (keliherSuiScaleOutput c b) _
    (keliherSuiScaleOutput_ne_zero c b hc hb)).1 hcount.symm).symm

/-- Transfer the translated-pair certificate to arbitrary affine
coordinates on a graph line. A surviving pair has the same count-four
parameter, and its coordinate values belong to the same 63-case list
after dividing the output coordinate by the direction ratio. -/
theorem keliherSui_affine_pair_prunes_or_exception
    (a b c o : Fin 256) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (e f : Fin 256 ≃ Fin 256)
    (hef : ∀ t, f t = keliherSuiMultiply c (keliherSuiXor (e t) o)) :
    let sp := e.symm (keliherSuiRowSpecial a)
    let sq := f.symm (keliherSuiColumnSpecial b)
    8 * ((∑ t : Fin 256, aesSboxDifferenceCountFin a (e t) *
      aesSboxDifferenceCountFin (f t) b) +
      7 * (if sp = sq then 16 else 8)) ≤ 3392 ∨
    (sp = sq ∧ (keliherSuiRowSpecial a,
      keliherSuiMultiply (keliherSuiInverse c) (keliherSuiColumnSpecial b)) ∈
      keliherSuiExceptionalPairs) := by
  dsimp only
  let b' := keliherSuiScaleOutput c b
  have hb' : b' ≠ 0 := keliherSuiScaleOutput_ne_zero c b hc hb
  have heq : e (f.symm (keliherSuiColumnSpecial b)) =
      keliherSuiXor (keliherSuiColumnSpecial b') o := by
    have h4 : aesSboxDifferenceCountFin
        (f (f.symm (keliherSuiColumnSpecial b))) b = 4 := by
      simpa using (keliherSuiColumnSpecial_spec b _ hb).2 rfl
    rw [hef, keliherSui_scaled_count c _ b hc] at h4
    exact (keliherSuiXor_eq_iff _ o _).1
      ((keliherSuiColumnSpecial_spec b' _ hb').1 h4)
  have hequal :
      keliherSuiRowSpecial a = keliherSuiXor (keliherSuiColumnSpecial b') o ↔
      e.symm (keliherSuiRowSpecial a) = f.symm (keliherSuiColumnSpecial b) := by
    rw [← heq]
    constructor
    · intro h
      apply e.injective
      simpa using h
    · intro h
      simpa using congrArg e h
  have hsum :
      (∑ t : Fin 256, aesSboxDifferenceCountFin a (e t) *
        aesSboxDifferenceCountFin (f t) b) =
      ∑ t : Fin 256, aesSboxDifferenceCountFin a t *
        aesSboxDifferenceCountFin (keliherSuiXor t o) b' := by
    apply Fintype.sum_equiv e
    intro t
    rw [hef, keliherSui_scaled_count c _ b hc]
  have h := keliherSui_translated_pair_prunes_or_exception a b' o ha hb'
  simp only [hequal] at h
  simpa only [← hsum, b', keliherSuiColumnSpecial_scaled c b hc hb] using h

end PairwiseIndependence

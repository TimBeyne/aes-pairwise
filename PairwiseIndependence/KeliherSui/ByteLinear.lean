import PairwiseIndependence.KeliherSui.Pair

/-!
# Byte-linear maps for the Keliher--Sui affine lines

Multiplication by a fixed AES field byte is an additive map. We use the
existing polynomial-basis AES implementation, without introducing a second
field representation or changing the S-box used in the theorem statements.
-/

namespace PairwiseIndependence

theorem aesXtime_iterate_add (n : Nat) (x y : AesByte) :
    (aesXtime^[n]) (x + y) = (aesXtime^[n]) x + (aesXtime^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', aesXtime_add] using
      congrArg aesXtime ih

theorem aesByteMul_add_left (x y c : AesByte) :
    aesByteMul (x + y) c = aesByteMul x c + aesByteMul y c := by
  unfold aesByteMul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · simp
  · exact aesXtime_iterate_add _ _ _

theorem aesByteMul_zero_left (c : AesByte) : aesByteMul 0 c = 0 := by
  have h := aesByteMul_add_left 0 0 c
  simpa only [zero_add, left_eq_add] using h

end PairwiseIndependence

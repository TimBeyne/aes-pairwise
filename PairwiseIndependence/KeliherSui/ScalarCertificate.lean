import PairwiseIndependence.KeliherSui.ByteLinear
import PairwiseIndependence.KeliherSui.AffinePairsSound

namespace PairwiseIndependence

/-- Numeric multiplication by the MixColumns coefficient `02`. -/
def aesFinXtime (t : Fin 256) : Fin 256 :=
  aesByteFinEquiv.symm (aesXtime (aesByteFinEquiv t))

theorem keliherSuiXor_join (x y z : Fin 256) :
    keliherSuiXor (keliherSuiXor x y) (keliherSuiXor y z) = keliherSuiXor x z := by
  apply aesByteFinEquiv.injective
  simp only [keliherSuiXor_byte]
  have hy : aesByteFinEquiv y + aesByteFinEquiv y = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [add_assoc, ← add_assoc (aesByteFinEquiv y), hy, zero_add]

def keliherSuiXorEquiv (o : Fin 256) : Fin 256 ≃ Fin 256 where
  toFun t := keliherSuiXor t o
  invFun t := keliherSuiXor t o
  left_inv t := keliherSuiXor_cancel t o
  right_inv t := keliherSuiXor_cancel t o

def keliherSuiXorList (xs : List (Fin 256)) : Fin 256 :=
  xs.foldr keliherSuiXor 0

theorem keliherSuiXorList_byte (xs : List (Fin 256)) :
    aesByteFinEquiv (keliherSuiXorList xs) = (xs.map aesByteFinEquiv).sum := by
  induction xs with
  | nil => exact (show aesByteFinEquiv (0 : Fin 256) = (0 : AesByte) by decide)
  | cons x xs ih =>
    simpa only [keliherSuiXorList, List.foldr_cons, List.map_cons,
      List.sum_cons, keliherSuiXor_byte] using congrArg (aesByteFinEquiv x + ·) ih

def keliherSuiXtimePowers (X : Array (Fin 256)) : Array (Array (Fin 256)) :=
  Array.ofFn (fun i : Fin 8 => Array.ofFn (fun t : Fin 256 =>
    ((fun z : Fin 256 => X[z.val]!)^[i.val]) t))

theorem keliherSuiXtimePowers_get (i : Fin 8) (t : Fin 256) :
    aesByteFinEquiv
      (((keliherSuiXtimePowers (Array.ofFn aesFinXtime))[i.val]!)[t.val]!) =
      (aesXtime^[i.val]) (aesByteFinEquiv t) := by
  simp only [keliherSuiXtimePowers, keliherSui_ofFn_get]
  have h (n : Nat) (t : Fin 256) :
      aesByteFinEquiv ((aesFinXtime^[n]) t) = (aesXtime^[n]) (aesByteFinEquiv t) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply', aesFinXtime, Equiv.apply_symm_apply, ih]
  exact h i.val t

def keliherSuiMultiplicationFromPowers (powers : Array (Array (Fin 256))) :
    Array (Array (Fin 256)) :=
  Array.ofFn (fun c : Fin 256 => Array.ofFn (fun t : Fin 256 =>
    keliherSuiXorList (List.ofFn (fun i : Fin 8 =>
      if aesByteFinEquiv c i = 0 then 0 else (powers[i.val]!)[t.val]!))))

def keliherSuiMultiplication : Array (Array (Fin 256)) :=
  keliherSuiMultiplicationFromPowers (keliherSuiXtimePowers (Array.ofFn aesFinXtime))

theorem keliherSuiMultiplicationFromPowers_get
    (powers : Array (Array (Fin 256))) (c t : Fin 256) :
    ((keliherSuiMultiplicationFromPowers powers)[c.val]!)[t.val]! =
      keliherSuiXorList (List.ofFn (fun i : Fin 8 =>
        if aesByteFinEquiv c i = 0 then 0 else (powers[i.val]!)[t.val]!)) := by
  simp only [keliherSuiMultiplicationFromPowers, keliherSui_ofFn_get]

def keliherSuiMultiply (c t : Fin 256) : Fin 256 :=
  (keliherSuiMultiplication[c.val]!)[t.val]!

theorem keliherSuiMultiply_byte (c t : Fin 256) :
    aesByteFinEquiv (keliherSuiMultiply c t) =
      aesByteMul (aesByteFinEquiv t) (aesByteFinEquiv c) := by
  simp only [keliherSuiMultiply, keliherSuiMultiplication, keliherSuiMultiplicationFromPowers_get,
    keliherSuiXorList_byte, List.map_ofFn, List.sum_ofFn]
  unfold aesByteMul
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  split_ifs
  · exact (show aesByteFinEquiv (0 : Fin 256) = (0 : AesByte) by decide)
  · exact keliherSuiXtimePowers_get i t

def keliherSuiInverse (c : Fin 256) : Fin 256 :=
  ⟨aesInverseTable[c.val]! % 256, Nat.mod_lt _ (by omega)⟩

def KeliherSuiMultiplicationInverseCheck (M : Array (Array (Fin 256))) : Prop :=
  ∀ c t : Fin 256, c ≠ 0 →
    (M[(keliherSuiInverse c).val]!)[((M[c.val]!)[t.val]!).val]! = t ∧
    (M[c.val]!)[((M[(keliherSuiInverse c).val]!)[t.val]!).val]! = t

instance (M : Array (Array (Fin 256))) : Decidable (KeliherSuiMultiplicationInverseCheck M) :=
  inferInstanceAs (Decidable (∀ c t : Fin 256, c ≠ 0 →
    (M[(keliherSuiInverse c).val]!)[((M[c.val]!)[t.val]!).val]! = t ∧
    (M[c.val]!)[((M[(keliherSuiInverse c).val]!)[t.val]!).val]! = t))

theorem keliherSuiMultiplication_inverse :
    KeliherSuiMultiplicationInverseCheck keliherSuiMultiplication := by native_decide

def keliherSuiMultiplyEquiv (c : Fin 256) (hc : c ≠ 0) : Fin 256 ≃ Fin 256 where
  toFun := keliherSuiMultiply c
  invFun := keliherSuiMultiply (keliherSuiInverse c)
  left_inv t := (keliherSuiMultiplication_inverse c t hc).1
  right_inv t := (keliherSuiMultiplication_inverse c t hc).2

theorem keliherSuiMultiply_zero (c : Fin 256) : keliherSuiMultiply c 0 = 0 := by
  apply aesByteFinEquiv.injective
  rw [keliherSuiMultiply_byte]
  have hz : aesByteFinEquiv (0 : Fin 256) = 0 := by decide
  rw [hz, aesByteMul_zero_left]

theorem keliherSuiMultiply_xor (c x y : Fin 256) :
    keliherSuiMultiply c (keliherSuiXor x y) =
      keliherSuiXor (keliherSuiMultiply c x) (keliherSuiMultiply c y) := by
  apply aesByteFinEquiv.injective
  simp only [keliherSuiMultiply_byte, keliherSuiXor_byte, aesByteMul_add_left]

def KeliherSuiMultiplicationCountsCheck (M : Array (Array (Fin 256)))
    (D : Array (Array Nat)) : Prop :=
  ∀ c t b : Fin 256, c ≠ 0 →
    (D[((M[c.val]!)[t.val]!).val]!)[b.val]! =
      (D[t.val]!)[((M[c.val]!)[b.val]!).val]!

instance (M : Array (Array (Fin 256))) (D : Array (Array Nat)) :
    Decidable (KeliherSuiMultiplicationCountsCheck M D) :=
  inferInstanceAs (Decidable (∀ c t b : Fin 256, c ≠ 0 →
    (D[((M[c.val]!)[t.val]!).val]!)[b.val]! =
      (D[t.val]!)[((M[c.val]!)[b.val]!).val]!))

theorem keliherSuiMultiplication_counts :
    KeliherSuiMultiplicationCountsCheck keliherSuiMultiplication
      aesInverseDifferenceCountTable := by native_decide

def keliherSuiScaleOutput (c b : Fin 256) : Fin 256 :=
  aesInverseAffineDifferenceIndex.symm
    (keliherSuiMultiply c (aesInverseAffineDifferenceIndex b))

theorem keliherSui_scaled_count (c t b : Fin 256) (hc : c ≠ 0) :
    aesSboxDifferenceCountFin (keliherSuiMultiply c t) b =
      aesSboxDifferenceCountFin t (keliherSuiScaleOutput c b) := by
  simp only [aesSboxDifferenceCountFin_index, keliherSuiScaleOutput,
    Equiv.apply_symm_apply]
  exact keliherSuiMultiplication_counts c t (aesInverseAffineDifferenceIndex b) hc

theorem keliherSuiScaleOutput_ne_zero (c b : Fin 256) (hc : c ≠ 0) (hb : b ≠ 0) :
    keliherSuiScaleOutput c b ≠ 0 := by
  intro h
  have hI : aesInverseAffineDifferenceIndex (0 : Fin 256) = 0 := by decide
  have h' := congrArg aesInverseAffineDifferenceIndex h
  simp only [keliherSuiScaleOutput, Equiv.apply_symm_apply, hI] at h'
  have h'' := congrArg (keliherSuiMultiply (keliherSuiInverse c)) h'
  have hinv : keliherSuiMultiply (keliherSuiInverse c)
      (keliherSuiMultiply c (aesInverseAffineDifferenceIndex b)) =
      aesInverseAffineDifferenceIndex b :=
    (keliherSuiMultiplication_inverse c (aesInverseAffineDifferenceIndex b) hc).1
  rw [hinv, keliherSuiMultiply_zero] at h''
  exact hb (aesInverseAffineDifferenceIndex.injective (h''.trans hI.symm))

end PairwiseIndependence

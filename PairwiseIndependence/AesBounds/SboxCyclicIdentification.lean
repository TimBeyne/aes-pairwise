import PairwiseIndependence.AesBounds.SboxCirculantPSD
import PairwiseIndependence.AES.ByteEncoding

/-!
# Comparing the cyclic certificate with inverse-byte difference counts

The finite computation in this module uses the inverse table already
certified against AES byte multiplication. It identifies the rational
certificate with the nonzero block of the concrete inverse-byte
difference-distribution matrix. `SboxNormTransfer` passes from this block to
the full matrix, and `SboxAffineBridge` through the affine output map.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

/-- Numeric multiplication by `03` in the AES polynomial byte field. -/
def aesMulThreeNat (x : Nat) : Nat :=
  Nat.xor x (if x < 128 then 2 * x else Nat.xor (2 * x - 256) 0x1b)

/-- The lookup-table form of the field inverse at a numeric byte. -/
theorem aesFieldInverse_ofNat (x : Fin 256) :
    aesFieldInverse (aesByteOfNat x.val) =
      aesByteOfNat (aesInverseTable[x.val]?.getD 0) := by
  simp only [aesFieldInverse, aesByteToNat_ofNat]

private theorem aesXor_lt (x y : Fin 256) : Nat.xor x.val y.val < 256 := by
  have h : ∀ x y : Fin 256, Nat.xor x.val y.val < 256 := by native_decide
  exact h x y

private def aesXorFin (x y : Fin 256) : Fin 256 :=
  ⟨Nat.xor x.val y.val, aesXor_lt x y⟩

private theorem aesInverseTable_value_lt (x : Fin 256) :
    aesInverseTable[x.val]! < 256 := by
  have h : ∀ x : Fin 256, aesInverseTable[x.val]! < 256 := by native_decide
  exact h x

private def aesInverseFin (x : Fin 256) : Fin 256 :=
  ⟨aesInverseTable[x.val]!, aesInverseTable_value_lt x⟩

private theorem aesInverseTable_getD (x : Fin 256) :
    aesInverseTable[x.val]?.getD 0 = aesInverseTable[x.val]! := by
  have h : ∀ x : Fin 256,
      aesInverseTable[x.val]?.getD 0 = aesInverseTable[x.val]! := by
    native_decide
  exact h x

private theorem aesFieldInverse_ofNat_eq (x : Fin 256) :
    aesFieldInverse (aesByteOfNat x.val) =
      aesByteOfNat (aesInverseFin x).val := by
  rw [aesFieldInverse_ofNat, aesInverseTable_getD]
  rfl

private theorem aesByteToNat_add_ofNat (x y : Fin 256) :
    aesByteToNat (aesByteOfNat x.val + aesByteOfNat y.val) =
      Nat.xor x.val y.val := by
  rw [← aesByteOfNat_xor x y]
  exact aesByteToNat_ofNat (aesXorFin x y)

/-- The direct numeric inverse-table difference agrees with the concrete
Lean inverse-byte output difference for every input and input difference. -/
theorem aesFieldInverse_difference_toNat (x a : Fin 256) :
    aesByteToNat
        (aesFieldInverse (aesByteOfNat (Nat.xor x.val a.val)) +
          aesFieldInverse (aesByteOfNat x.val)) =
      Nat.xor aesInverseTable[x.val]!
        aesInverseTable[Nat.xor x.val a.val]! := by
  calc
    aesByteToNat
        (aesFieldInverse (aesByteOfNat (Nat.xor x.val a.val)) +
          aesFieldInverse (aesByteOfNat x.val)) =
        aesByteToNat
          (aesByteOfNat (aesInverseFin (aesXorFin x a)).val +
            aesByteOfNat (aesInverseFin x).val) := by
      rw [show Nat.xor x.val a.val = (aesXorFin x a).val by rfl,
        aesFieldInverse_ofNat_eq, aesFieldInverse_ofNat_eq]
    _ = Nat.xor (aesInverseFin (aesXorFin x a)).val
          (aesInverseFin x).val :=
      aesByteToNat_add_ofNat _ _
    _ = Nat.xor aesInverseTable[x.val]!
          aesInverseTable[Nat.xor x.val a.val]! := by
      simp only [aesInverseFin, aesXorFin]
      exact Nat.xor_comm _ _

private theorem aesByteToNat_eq_iff (y : AesByte) (b : Fin 256) :
    aesByteToNat y = b.val ↔ y = aesByteOfNat b.val := by
  constructor
  · intro h
    calc
      y = aesByteOfNat (aesByteToNat y) := (aesByteOfNat_toNat y).symm
      _ = aesByteOfNat b.val := by rw [h]
  · intro h
    rw [h]
    exact aesByteToNat_ofNat b

private theorem aesByte_charTwo_eq_add_iff (u v b : AesByte) :
    u = v + b ↔ u + v = b := by
  have hself (w : AesByte) : w + w = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (w i)
  constructor
  · intro h
    rw [h]
    calc
      (v + b) + v = (v + v) + b := by abel
      _ = b := by rw [hself, zero_add]
  · intro h
    calc
      u = (u + v) + v := by rw [add_assoc, hself, add_zero]
      _ = b + v := by rw [h]
      _ = v + b := by abel

/-- The integer lookup-table condition is precisely the concrete Lean
inverse-byte differential condition under the numeric byte encoding. -/
theorem aesFieldInverse_difference_condition (x a b : Fin 256) :
    Nat.xor aesInverseTable[x.val]!
        aesInverseTable[Nat.xor x.val a.val]! = b.val ↔
      aesFieldInverse (aesByteOfNat x.val + aesByteOfNat a.val) =
        aesFieldInverse (aesByteOfNat x.val) + aesByteOfNat b.val := by
  let u := aesFieldInverse (aesByteOfNat x.val + aesByteOfNat a.val)
  let v := aesFieldInverse (aesByteOfNat x.val)
  have hnum : aesByteToNat (u + v) =
      Nat.xor aesInverseTable[x.val]!
        aesInverseTable[Nat.xor x.val a.val]! := by
    simpa only [u, v, aesByteOfNat_xor x a] using
      aesFieldInverse_difference_toNat x a
  calc
    Nat.xor aesInverseTable[x.val]!
        aesInverseTable[Nat.xor x.val a.val]! = b.val ↔
        aesByteToNat (u + v) = b.val := by rw [hnum]
    _ ↔ u + v = aesByteOfNat b.val := aesByteToNat_eq_iff _ _
    _ ↔ u = v + aesByteOfNat b.val :=
      (aesByte_charTwo_eq_add_iff _ _ _).symm

/-- The 255 nonzero byte values in consecutive powers of the byte-field
element `03`, computed using numeric byte arithmetic. The numeric operation
is checked against the certified AES multiplication below. -/
def aesBytePowersOfThree : Array Nat := Id.run do
  let mut powers : Array Nat := #[]
  let mut x : Nat := 1
  for _ in [:255] do
    powers := powers.push x
    x := aesMulThreeNat x
  return powers

/-- The inverse byte table's differential counts, with input difference
indexing the outer array and output difference indexing the inner one. -/
def aesInverseDifferenceCountTable : Array (Array Nat) := Id.run do
  let inverse := aesInverseTable
  let mut table := Array.replicate 256 (Array.replicate 256 0)
  for a in [:256] do
    let mut row := table[a]!
    for x in [:256] do
      let y := Nat.xor inverse[x]! inverse[Nat.xor x a]!
      row := row.set! y (row[y]! + 1)
    table := table.set! a row
  return table

/-- Each nonzero AES byte occurs exactly once in the power order. -/
theorem aesBytePowersOfThree_nodup_and_nonzero :
    let powers := aesBytePowersOfThree
    powers.size = 255 ∧
      powers.toList.Nodup ∧
      ∀ i : Fin 255, powers[i.val]! ≠ 0 := by
  native_decide

theorem aesBytePowersOfThree_lt (i : Fin 255) :
    aesBytePowersOfThree[i.val]! < 256 := by
  have h : ∀ i : Fin 255, aesBytePowersOfThree[i.val]! < 256 := by
    native_decide
  exact h i

/-- The actual Lean AES byte at a nonzero power of `03`. -/
def aesPowerByte (i : ZMod 255) : AesByte :=
  aesByteOfNat aesBytePowersOfThree[i.val]!

theorem aesPowerByte_ne_zero (i : ZMod 255) : aesPowerByte i ≠ 0 := by
  have hnonzero := aesBytePowersOfThree_nodup_and_nonzero.2.2
    ⟨i.val, ZMod.val_lt i⟩
  intro hzero
  have hnat := congrArg aesByteToNat hzero
  have hcode := aesByteToNat_ofNat
    ⟨aesBytePowersOfThree[i.val]!,
      aesBytePowersOfThree_lt ⟨i.val, ZMod.val_lt i⟩⟩
  simp only [aesPowerByte, hcode] at hnat
  have hzeroNat : aesByteToNat (0 : AesByte) = 0 := by
    decide
  rw [hzeroNat] at hnat
  exact hnonzero hnat

/-- The imperative count table agrees with the direct differential count of
the certified inverse lookup table. Both arrays are shared across the
finite computation. -/
theorem aesInverseDifferenceCountTable_eq_sum :
    let counts := aesInverseDifferenceCountTable
    let inverse := aesInverseTable
    ∀ a b : Fin 256,
      (counts[a.val]!)[b.val]! =
        ∑ x : Fin 256,
          if Nat.xor inverse[x.val]! inverse[Nat.xor x.val a.val]! = b.val
          then 1 else 0 := by
  native_decide

/-- The numeric difference-count table is exactly the count of concrete
Lean `aesFieldInverse` differentials. -/
theorem aesInverseDifferenceCountTable_eq_byte_sum (a b : Fin 256) :
    (aesInverseDifferenceCountTable[a.val]!)[b.val]! =
      ∑ x : AesByte,
        if aesFieldInverse (x + aesByteOfNat a.val) =
            aesFieldInverse x + aesByteOfNat b.val
        then 1 else 0 := by
  rw [aesInverseDifferenceCountTable_eq_sum]
  exact Fintype.sum_equiv aesByteFinEquiv _ _ (fun x => by
    simp only [aesByteFinEquiv, Equiv.coe_fn_mk]
    simp only [aesFieldInverse_difference_condition x a b])

/-- The actual difference-distribution matrix of the certified Lean inverse
byte map has the integer count table as its numerator. -/
theorem aesFieldInverse_differenceDistributionMatrix_entry (a b : Fin 256) :
    deterministicDifferenceDistributionMatrix aesFieldInverse
        (aesByteOfNat b.val) (aesByteOfNat a.val) =
      ((aesInverseDifferenceCountTable[a.val]!)[b.val]! : ℝ) / 256 := by
  classical
  have hcount := aesInverseDifferenceCountTable_eq_byte_sum a b
  have hcast :
      (∑ x : AesByte,
        if aesFieldInverse (x + aesByteOfNat a.val) =
            aesFieldInverse x + aesByteOfNat b.val
        then (1 : ℝ) else 0) =
        ((aesInverseDifferenceCountTable[a.val]!)[b.val]! : ℝ) := by
    exact_mod_cast hcount.symm
  simp only [deterministicDifferenceDistributionMatrix,
    differenceDistributionMatrix]
  simp
  convert congrArg (fun z : ℝ => z / 256) hcast using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : aesFieldInverse (x + aesByteOfNat a.val) =
      aesFieldInverse x + aesByteOfNat b.val <;> simp [hx]

/-- The inverse-byte difference counts are cyclic when both nonzero input
and output differences are indexed by powers of `03`. The count table and
power order are evaluated once for this 255×255 integer check. -/
theorem aesInverseDifferenceCountTable_cyclic :
    let counts := aesInverseDifferenceCountTable
    let powers := aesBytePowersOfThree
    ∀ i k : Fin 255,
      (counts[powers[i.val]!]!)[powers[k.val]!]! =
        (counts[1]!)[powers[(i.val + k.val) % 255]!]! := by
  native_decide

/-- The first row of the centered inverse-byte Gram matrix agrees exactly
with the listed cyclic coefficient numerators. Only 255 inner products of
255 entries are computed, instead of all 255² inner products. -/
theorem aesInverseCyclicGramFirstRow_eq_certificate :
    let counts := aesInverseDifferenceCountTable
    let powers := aesBytePowersOfThree
    ∀ k : Fin 255,
      (∑ b : Fin 255,
        (((counts[1]!)[powers[b.val]!]! : Int) * 255 - 256) *
          (((counts[powers[k.val]!]!)[powers[b.val]!]! : Int) * 255 - 256)) =
        aesSboxCyclicGramNumerator k := by
  native_decide

/-- The centered integer difference count for two nonzero differences,
indexed by powers of `03`. Dividing by `65280 = 255 · 256` gives the
corresponding centered difference-distribution-matrix entry. -/
def aesInverseCountAtPowers (i k : Nat) : Nat :=
  let a := aesBytePowersOfThree[i]!
  let b := aesBytePowersOfThree[k]!
  let row := aesInverseDifferenceCountTable[a]!
  row[b]!

def aesInverseCenteredCount (i k : ZMod 255) : Int :=
  (aesInverseCountAtPowers i.val k.val : Int) * 255 - 256

private def aesInverseCenteredCountBase (k : ZMod 255) : Int :=
  ((aesInverseDifferenceCountTable[1]!)[aesBytePowersOfThree[k.val]!]! : Int) *
    255 - 256

private theorem aesInverseCenteredCount_cyclic (i k : ZMod 255) :
    aesInverseCenteredCount i k = aesInverseCenteredCountBase (i + k) := by
  have h := aesInverseDifferenceCountTable_cyclic
    ⟨i.val, ZMod.val_lt i⟩ ⟨k.val, ZMod.val_lt k⟩
  change (aesInverseCountAtPowers i.val k.val : Int) * 255 - 256 =
    ((aesInverseDifferenceCountTable[1]!)[aesBytePowersOfThree[(i + k).val]!]! : Int) *
      255 - 256
  exact congrArg (fun n : Nat => (n : Int) * 255 - 256)
    (by simpa only [aesInverseCountAtPowers, ZMod.val_add] using h)

/-- The complete centered integer Gram matrix of the numeric inverse-byte
difference counts is the cyclic coefficient table. The only finite checks
are the cyclic 255×255 count identity and the 255 entries of its first Gram
row; all other Gram entries follow by reindexing a sum. -/
theorem aesInverseCenteredCount_gram_eq_certificate (i j : ZMod 255) :
    (∑ k : ZMod 255,
      aesInverseCenteredCount i k * aesInverseCenteredCount j k) =
        aesSboxCyclicGramNumerator
          ((ZMod.finEquiv 255).symm (j - i)) := by
  have hbij : Function.Bijective (fun k : ZMod 255 => i + k) :=
    AddGroup.addLeft_bijective i
  have hshift :
      (∑ k : ZMod 255,
        aesInverseCenteredCount i k * aesInverseCenteredCount j k) =
        ∑ k : ZMod 255,
          aesInverseCenteredCountBase k *
            aesInverseCenteredCount (j - i) k := by
    calc
      (∑ k : ZMod 255,
          aesInverseCenteredCount i k * aesInverseCenteredCount j k) =
          ∑ k : ZMod 255,
            aesInverseCenteredCountBase (i + k) *
              aesInverseCenteredCount (j - i) (i + k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [aesInverseCenteredCount_cyclic i k,
          aesInverseCenteredCount_cyclic j k,
          aesInverseCenteredCount_cyclic (j - i) (i + k)]
        rw [show j + k = (j - i) + (i + k) by abel]
      _ = ∑ k : ZMod 255,
            aesInverseCenteredCountBase k *
              aesInverseCenteredCount (j - i) k :=
        Fintype.sum_bijective (fun k : ZMod 255 => i + k) hbij
          (fun k => aesInverseCenteredCountBase (i + k) *
            aesInverseCenteredCount (j - i) (i + k))
          (fun k => aesInverseCenteredCountBase k *
            aesInverseCenteredCount (j - i) k)
          (fun k => rfl)
  rw [hshift]
  let e := ZMod.finEquiv 255
  have hfirst := aesInverseCyclicGramFirstRow_eq_certificate
    (e.symm (j - i))
  have hsum := Fintype.sum_equiv e
    (fun k : Fin 255 =>
      aesInverseCenteredCountBase (e k) *
        aesInverseCenteredCount (j - i) (e k))
    (fun k : ZMod 255 =>
      aesInverseCenteredCountBase k *
        aesInverseCenteredCount (j - i) k)
    (fun k => by simp)
  rw [← hsum]
  simpa only [aesInverseCenteredCount, aesInverseCenteredCountBase,
    aesInverseCountAtPowers, e, ZMod.finEquiv, Equiv.apply_symm_apply] using hfirst

/-- The nonzero-difference block of the centered inverse-table difference
matrix, in the `03` power order. Its entries are the integer differential
counts divided by 256, minus the uniform value `1/255`. -/
noncomputable def aesInverseCenteredNumericMatrix :
    Matrix (ZMod 255) (ZMod 255) ℝ :=
  fun b a => (aesInverseCenteredCount a b : ℝ) / 65280

/-- The finite inverse-table count identity gives precisely the Gram matrix
whose rational positive-semidefinite certificate was checked above. -/
theorem aesInverseCenteredNumericMatrix_gram :
    aesInverseCenteredNumericMatrixᴴ * aesInverseCenteredNumericMatrix =
      aesSboxCyclicGramRealMatrix := by
  ext i j
  calc
    (aesInverseCenteredNumericMatrixᴴ * aesInverseCenteredNumericMatrix) i j =
        (∑ k : ZMod 255,
          (aesInverseCenteredCount i k : ℝ) *
            (aesInverseCenteredCount j k : ℝ)) / (65280 : ℝ) ^ 2 := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        star_trivial, aesInverseCenteredNumericMatrix]
      rw [Finset.sum_div]
      congr 1
      funext k
      ring
    _ = (aesSboxCyclicGramNumerator
          ((ZMod.finEquiv 255).symm (j - i)) : ℝ) / (65280 : ℝ) ^ 2 := by
      congr 1
      exact_mod_cast aesInverseCenteredCount_gram_eq_certificate i j
    _ = aesSboxCyclicGramRealMatrix i j := by
      norm_num [aesSboxCyclicGramRealMatrix, aesSboxCyclicGramCoefficient]

/-- The numeric inverse-table centered difference matrix satisfies the
slightly relaxed one-byte norm bound used by the cyclic certificate. -/
theorem aesInverseCenteredNumericMatrix_norm_le :
    ‖aesInverseCenteredNumericMatrix‖ ≤ (70315 : ℝ) / 1000000 :=
  aesSboxCyclicGram_norm_le _ aesInverseCenteredNumericMatrix_gram

/-- The certified numeric centered matrix is literally the nonzero-byte
block of the concrete Lean inverse-byte difference-distribution matrix. -/
theorem aesInverseCenteredNumericMatrix_eq_inverseDifferenceDistributionBlock
    (b a : ZMod 255) :
    aesInverseCenteredNumericMatrix b a =
      (deterministicDifferenceDistributionMatrix aesFieldInverse -
        uniformDifferenceDistributionMatrix AesByte)
          (aesPowerByte b) (aesPowerByte a) := by
  let ai : Fin 256 :=
    ⟨aesBytePowersOfThree[a.val]!,
      aesBytePowersOfThree_lt ⟨a.val, ZMod.val_lt a⟩⟩
  let bi : Fin 256 :=
    ⟨aesBytePowersOfThree[b.val]!,
      aesBytePowersOfThree_lt ⟨b.val, ZMod.val_lt b⟩⟩
  have hD := aesFieldInverse_differenceDistributionMatrix_entry ai bi
  have hU : uniformDifferenceDistributionMatrix AesByte
      (aesPowerByte b) (aesPowerByte a) = (1 : ℝ) / 255 := by
    simp [uniformDifferenceDistributionMatrix_apply,
      aesPowerByte_ne_zero a, aesPowerByte_ne_zero b]
  simp only [Matrix.sub_apply, hU]
  change (aesInverseCenteredCount a b : ℝ) / 65280 =
    deterministicDifferenceDistributionMatrix aesFieldInverse
        (aesPowerByte b) (aesPowerByte a) - 1 / 255
  rw [show deterministicDifferenceDistributionMatrix aesFieldInverse
      (aesPowerByte b) (aesPowerByte a) =
        ((aesInverseDifferenceCountTable[ai.val]!)[bi.val]! : ℝ) / 256 by
      simpa only [aesPowerByte, ai, bi] using hD]
  simp only [aesInverseCenteredCount, aesInverseCountAtPowers,
    ai, bi]
  push_cast
  ring

end PairwiseIndependence

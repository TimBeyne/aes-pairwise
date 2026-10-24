import PairwiseIndependence.AesBounds.SboxCyclicIdentification

/-!
# Transferring the inverse-byte bound to the full difference matrix

The exact finite Gram certificate is proved in the preceding modules. Here
the nonzero byte order is packaged as an equivalence so that zero-difference
coordinates can be separated from the certified block.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

private theorem aesBytePowersOfThree_injective :
    let powers := aesBytePowersOfThree
    ∀ i j : Fin 255, powers[i.val]! = powers[j.val]! → i = j := by
  native_decide

private theorem aesBytePowersOfThree_cover :
    let powers := aesBytePowersOfThree
    ∀ x : Fin 256, x.val ≠ 0 →
      ∃ i : Fin 255, powers[i.val]! = x.val := by
  native_decide

theorem aesPowerByte_injective : Function.Injective aesPowerByte := by
  intro i j h
  have hi : aesBytePowersOfThree[i.val]! < 256 :=
    aesBytePowersOfThree_lt ⟨i.val, ZMod.val_lt i⟩
  have hj : aesBytePowersOfThree[j.val]! < 256 :=
    aesBytePowersOfThree_lt ⟨j.val, ZMod.val_lt j⟩
  have hnat : aesBytePowersOfThree[i.val]! =
      aesBytePowersOfThree[j.val]! := by
    have heq := congrArg aesByteToNat h
    simpa only [aesPowerByte,
      aesByteToNat_ofNat ⟨_, hi⟩,
      aesByteToNat_ofNat ⟨_, hj⟩] using heq
  have hfin := aesBytePowersOfThree_injective
    ⟨i.val, ZMod.val_lt i⟩ ⟨j.val, ZMod.val_lt j⟩ hnat
  exact ZMod.val_injective 255 (congrArg Fin.val hfin)

/-- The `03` power order enumerates precisely the nonzero concrete AES
bytes. -/
noncomputable def aesPowerByteNonzeroEquiv :
    ZMod 255 ≃ {x : AesByte // x ≠ 0} :=
  Equiv.ofBijective
    (fun i => ⟨aesPowerByte i, aesPowerByte_ne_zero i⟩)
    (by
      constructor
      · intro i j h
        exact aesPowerByte_injective (congrArg Subtype.val h)
      · intro y
        let n : Fin 256 :=
          ⟨aesByteToNat y.val, aesByteToNat_lt y.val⟩
        have hn : n.val ≠ 0 := by
          intro hzero
          apply y.property
          calc
            y.val = aesByteOfNat (aesByteToNat y.val) :=
              (aesByteOfNat_toNat y.val).symm
            _ = 0 := by
              change aesByteToNat y.val = 0 at hzero
              rw [hzero]
              funext k
              simp [aesByteOfNat]
        obtain ⟨i, hi⟩ := aesBytePowersOfThree_cover n hn
        refine ⟨(ZMod.finEquiv 255) i, ?_⟩
        apply Subtype.ext
        change aesPowerByte ((ZMod.finEquiv 255) i) = y.val
        calc
          aesPowerByte ((ZMod.finEquiv 255) i) =
              aesByteOfNat aesBytePowersOfThree[i.val]! := by rfl
          _ = aesByteOfNat n.val := by rw [hi]
          _ = y.val := aesByteOfNat_toNat y.val)

/-- The centered inverse-byte difference-distribution matrix on all 256
byte differences. -/
noncomputable def aesInverseCenteredFullMatrix :
    Matrix AesByte AesByte ℝ :=
  deterministicDifferenceDistributionMatrix aesFieldInverse -
    uniformDifferenceDistributionMatrix AesByte

private theorem aesInverseCenteredFullMatrix_zero_column (b : AesByte) :
    aesInverseCenteredFullMatrix b 0 = 0 := by
  change differenceDistributionMatrix
      (fun _ : Unit => aesFieldInverse) b 0 -
        uniformDifferenceDistributionMatrix AesByte b 0 = 0
  rw [differenceDistributionMatrix_zero_input]
  by_cases hb : b = 0 <;>
    simp [uniformDifferenceDistributionMatrix_apply, hb]

private theorem aesInverseCenteredFullMatrix_zero_row (a : AesByte) :
    aesInverseCenteredFullMatrix 0 a = 0 := by
  by_cases ha : a = 0
  · subst a
    exact aesInverseCenteredFullMatrix_zero_column 0
  · have hinj : Function.Injective aesFieldInverse :=
      Function.Involutive.injective aesFieldInverse_involutive
    have hD : differenceDistributionMatrix
        (fun _ : Unit => aesFieldInverse) 0 a = 0 :=
      differenceDistributionMatrix_zero_output _
        (by intro _; exact hinj) ha
    simp [aesInverseCenteredFullMatrix,
      deterministicDifferenceDistributionMatrix, hD,
      uniformDifferenceDistributionMatrix_apply, ha]

/-- The coordinate embedding of the 255 nonzero byte differences. -/
noncomputable def aesPowerEmbedding :
    Matrix AesByte (ZMod 255) ℝ :=
  fun x i => if x = aesPowerByte i then 1 else 0

private theorem aesPowerEmbedding_apply_power (i j : ZMod 255) :
    aesPowerEmbedding (aesPowerByte i) j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [aesPowerEmbedding]
  · have hbyte : aesPowerByte i ≠ aesPowerByte j :=
      fun h => hij (aesPowerByte_injective h)
    simp [aesPowerEmbedding, hij, hbyte]

private theorem aesPowerEmbedding_apply_zero (i : ZMod 255) :
    aesPowerEmbedding 0 i = 0 := by
  simp [aesPowerEmbedding, (aesPowerByte_ne_zero i).symm]

/-- Columns of the nonzero-byte embedding are orthonormal. -/
theorem aesPowerEmbedding_gram :
    aesPowerEmbeddingᴴ * aesPowerEmbedding = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  calc
    (∑ x : AesByte, aesPowerEmbedding x i * aesPowerEmbedding x j) =
        aesPowerEmbedding (aesPowerByte i) j := by
      rw [Finset.sum_eq_single (aesPowerByte i)]
      · simp [aesPowerEmbedding]
      · intro x _ hx
        simp [aesPowerEmbedding, hx]
      · intro hx
        exact False.elim (hx (Finset.mem_univ _))
    _ = (1 : Matrix (ZMod 255) (ZMod 255) ℝ) i j := by
      simp [aesPowerEmbedding_apply_power, Matrix.one_apply]

theorem aesPowerEmbedding_norm_le_one : ‖aesPowerEmbedding‖ ≤ 1 := by
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self aesPowerEmbedding
  rw [aesPowerEmbedding_gram, norm_one] at hnorm
  nlinarith [norm_nonneg aesPowerEmbedding]

private theorem aesPowerEmbedding_mul_apply_power
    (B : Matrix (ZMod 255) (ZMod 255) ℝ) (i j : ZMod 255) :
    (aesPowerEmbedding * B) (aesPowerByte i) j = B i j := by
  simp [Matrix.mul_apply, aesPowerEmbedding_apply_power]

private theorem aesPowerEmbedding_mul_apply_zero
    (B : Matrix (ZMod 255) (ZMod 255) ℝ) (j : ZMod 255) :
    (aesPowerEmbedding * B) 0 j = 0 := by
  simp [Matrix.mul_apply, aesPowerEmbedding_apply_zero]

private theorem aesPowerEmbedding_mul_conjTranspose_apply_power
    (B : Matrix (ZMod 255) (ZMod 255) ℝ)
    (x : AesByte) (j : ZMod 255) :
    (aesPowerEmbedding * B * aesPowerEmbeddingᴴ) x
      (aesPowerByte j) = (aesPowerEmbedding * B) x j := by
  simp [Matrix.mul_apply,
    aesPowerEmbedding_apply_power]

private theorem aesPowerEmbedding_mul_conjTranspose_zero_column
    (B : Matrix (ZMod 255) (ZMod 255) ℝ) (x : AesByte) :
    (aesPowerEmbedding * B * aesPowerEmbeddingᴴ) x 0 = 0 := by
  simp [Matrix.mul_apply,
    aesPowerEmbedding_apply_zero]

/-- The full centered inverse-byte matrix is the certified 255×255 block
embedded into the nonzero byte coordinates, with a zero row and column. -/
theorem aesInverseCenteredFullMatrix_factorization :
    aesInverseCenteredFullMatrix =
      aesPowerEmbedding * aesInverseCenteredNumericMatrix *
        aesPowerEmbeddingᴴ := by
  ext x y
  by_cases hx : x = 0
  · subst x
    rw [aesInverseCenteredFullMatrix_zero_row]
    rw [Matrix.mul_apply]
    simp [aesPowerEmbedding_mul_apply_zero]
  by_cases hy : y = 0
  · subst y
    rw [aesInverseCenteredFullMatrix_zero_column]
    exact (aesPowerEmbedding_mul_conjTranspose_zero_column _ _).symm
  obtain ⟨i, hi⟩ := aesPowerByteNonzeroEquiv.surjective
    (⟨x, hx⟩ : {z : AesByte // z ≠ 0})
  obtain ⟨j, hj⟩ := aesPowerByteNonzeroEquiv.surjective
    (⟨y, hy⟩ : {z : AesByte // z ≠ 0})
  have hxi : aesPowerByte i = x := congrArg Subtype.val hi
  have hyj : aesPowerByte j = y := congrArg Subtype.val hj
  rw [← hxi, ← hyj,
    aesPowerEmbedding_mul_conjTranspose_apply_power,
    aesPowerEmbedding_mul_apply_power]
  exact (aesInverseCenteredNumericMatrix_eq_inverseDifferenceDistributionBlock i j).symm

/-- The one-byte inverse map satisfies the certified full difference-matrix
bound. This is the first unconditional one-byte norm statement connected to
the concrete Lean byte permutation. -/
theorem aesFieldInverse_differenceDistributionMatrix_norm_le :
    ‖deterministicDifferenceDistributionMatrix aesFieldInverse -
        uniformDifferenceDistributionMatrix AesByte‖ ≤
      (70315 : ℝ) / 1000000 := by
  change ‖aesInverseCenteredFullMatrix‖ ≤ _
  rw [aesInverseCenteredFullMatrix_factorization]
  have hP := aesPowerEmbedding_norm_le_one
  have hPT : ‖aesPowerEmbeddingᴴ‖ ≤ (1 : ℝ) := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hP
  have hsq : ‖aesPowerEmbedding‖ * ‖aesPowerEmbeddingᴴ‖ ≤ 1 := by
    nlinarith [norm_nonneg aesPowerEmbedding,
      norm_nonneg aesPowerEmbeddingᴴ]
  calc
    ‖aesPowerEmbedding * aesInverseCenteredNumericMatrix *
        aesPowerEmbeddingᴴ‖ ≤
        ‖aesPowerEmbedding * aesInverseCenteredNumericMatrix‖ *
          ‖aesPowerEmbeddingᴴ‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖aesPowerEmbedding‖ *
          ‖aesInverseCenteredNumericMatrix‖) *
          ‖aesPowerEmbeddingᴴ‖ :=
      mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = (‖aesPowerEmbedding‖ * ‖aesPowerEmbeddingᴴ‖) *
          ‖aesInverseCenteredNumericMatrix‖ := by ring
    _ ≤ ‖aesInverseCenteredNumericMatrix‖ := by
      calc
        (‖aesPowerEmbedding‖ * ‖aesPowerEmbeddingᴴ‖) *
            ‖aesInverseCenteredNumericMatrix‖ ≤
            1 * ‖aesInverseCenteredNumericMatrix‖ :=
          mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
        _ = ‖aesInverseCenteredNumericMatrix‖ := one_mul _
    _ ≤ (70315 : ℝ) / 1000000 :=
      aesInverseCenteredNumericMatrix_norm_le

end PairwiseIndependence

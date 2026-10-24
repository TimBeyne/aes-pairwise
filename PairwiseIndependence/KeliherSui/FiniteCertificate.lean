import PairwiseIndependence.KeliherSui.Estimates

/-!
# Exact finite obligation for the Keliher--Sui upper bound

The universal `53 / 2^34` claim can be checked entirely with natural-number
arithmetic on the certified AES byte difference-count table. This file proves
that reduction. `KeliherSui/UpperBound.lean` proves the resulting integer
inequality via the sharp affine five-list certificate.
-/

namespace PairwiseIndependence

/-- Number of inputs to the actual AES S-box with input difference `a` and
output difference `b`, obtained from the inverse-byte table by the affine
output-difference permutation. -/
def aesSboxDifferenceCount (a b : AesByte) : Nat :=
  (aesInverseDifferenceCountTable[aesByteToNat a]!)[
    aesByteToNat (aesAffineLinearEquiv.symm b)]!

/-- A zero input difference propagates only to zero, with all 256 byte
values counted. -/
theorem aesSboxDifferenceCount_zero_input :
    ∀ b : AesByte,
      aesSboxDifferenceCount 0 b = if b = 0 then 256 else 0 := by
  native_decide

/-- Since the AES S-box is a permutation, zero output difference requires
zero input difference. -/
theorem aesSboxDifferenceCount_zero_output :
    ∀ a : AesByte,
      aesSboxDifferenceCount a 0 = if a = 0 then 256 else 0 := by
  native_decide

/-- The AES affine output map reindexes inverse-byte output differences.
Keeping this explicit lets the row/column profiles transfer symbolically. -/
def aesInverseAffineDifferenceIndex : Fin 256 ≃ Fin 256 :=
  (aesByteFinEquiv.trans aesAffineLinearEquiv.symm.toEquiv).trans
    aesByteFinEquiv.symm

/-- The exact integer numerator of a two-round four-byte superbox
difference-distribution entry. The denominator is `256^8`: four byte
probabilities before MixColumns and four after it. -/
def keliherSuiSuperboxNumerator (a b : State AesByte 4) : Nat :=
  ∑ x : State AesByte 4,
    (∏ i : Fin 4, aesSboxDifferenceCount (a i) (x i)) *
      ∏ i : Fin 4,
        aesSboxDifferenceCount (aesMixColumnEquiv x i) (b i)

/-- The MDS branch number makes every nontrivial superbox differential with
fewer than five active endpoint bytes impossible. This eliminates the first
support class before any numerical pruning. -/
theorem keliherSuiSuperboxNumerator_eq_zero_of_low_activity
    (a b : State AesByte 4) (ha : a ≠ 0)
    (hactivity : activeCoordinates a + activeCoordinates b ≤ 4) :
    keliherSuiSuperboxNumerator a b = 0 := by
  classical
  unfold keliherSuiSuperboxNumerator
  apply Finset.sum_eq_zero
  intro x _
  by_contra hterm
  have hfirst :
      (∏ i : Fin 4, aesSboxDifferenceCount (a i) (x i)) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hterm).1
  have hsecond :
      (∏ i : Fin 4,
        aesSboxDifferenceCount (aesMixColumnEquiv x i) (b i)) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hterm).2
  have hxin (i : Fin 4) : x i ≠ 0 → a i ≠ 0 := by
    intro hxi hai
    have hf := (Finset.prod_ne_zero_iff.mp hfirst) i (Finset.mem_univ i)
    rw [hai, aesSboxDifferenceCount_zero_input] at hf
    simp [hxi] at hf
  have hyout (i : Fin 4) : (aesMixColumnEquiv x) i ≠ 0 → b i ≠ 0 := by
    intro hyi hbi
    have hf := (Finset.prod_ne_zero_iff.mp hsecond) i (Finset.mem_univ i)
    rw [hbi, aesSboxDifferenceCount_zero_output] at hf
    simp [hyi] at hf
  have hx : x ≠ 0 := by
    intro hx
    apply ha
    funext i
    change a i = 0
    by_contra hai
    have hf := (Finset.prod_ne_zero_iff.mp hfirst) i (Finset.mem_univ i)
    rw [hx, Pi.zero_apply, aesSboxDifferenceCount_zero_output] at hf
    simp [hai] at hf
  have hxle : activeCoordinates x ≤ activeCoordinates a := by
    unfold activeCoordinates
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hxin i hi
  have hyle : activeCoordinates (aesMixColumnEquiv x) ≤
      activeCoordinates b := by
    unfold activeCoordinates
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hyout i hi
  have hbranch := aesMixColumn_isMDS x hx
  omega

/-- The exact computational claim needed for the paper's two-round upper
bound, expressed without real arithmetic or an opaque cryptographic assumption.
The proof is `keliherSui_finiteUpperCertificate` in `KeliherSui/UpperBound.lean`. -/
def KeliherSuiFiniteUpperCertificate : Prop :=
  ∀ a b : State AesByte 4, a ≠ 0 →
    keliherSuiSuperboxNumerator a b ≤ 53 * 2 ^ 30

theorem aesIndependentSuperbox_differenceDistributionMatrix_eq_finiteCount
    (a b : State AesByte 4) :
    differenceDistributionMatrix
      (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
        b a = (keliherSuiSuperboxNumerator a b : ℝ) / 256 ^ 8 := by
  rw [aesIndependentSuperbox_differenceDistributionMatrix_eq_sharkTwoCore]
  rw [sharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct]
  unfold keliherSuiSuperboxNumerator
  have hpoint (x : State AesByte 4) :
      (∏ j : Sum (Fin 4) (Fin 4),
        (Sum.elim
          (fun i z => deterministicDifferenceDistributionMatrix aesSboxEquiv z (a i))
          (fun i z => deterministicDifferenceDistributionMatrix aesSboxEquiv (b i) z)
          j) (mdsGraphCoordinate aesMixColumnEquiv x j)) =
        (((∏ i : Fin 4, aesSboxDifferenceCount (a i) (x i)) *
          ∏ i : Fin 4,
            aesSboxDifferenceCount (aesMixColumnEquiv x i) (b i) : Nat) : ℝ) /
          256 ^ 8 := by
    simp only [Fintype.prod_sum_type, mdsGraphCoordinate,
      Sum.elim_inl, Sum.elim_inr]
    simp only [aesSboxEquiv, Equiv.coe_fn_mk]
    simp_rw [aesSbox_differenceDistributionMatrix_eq_count]
    dsimp only [aesSboxDifferenceCount]
    simp only [Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_fin, Nat.cast_mul, Nat.cast_prod]
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  simp only [Nat.cast_sum]

/-- A finite certificate implies the named Keliher--Sui two-round estimate
used by Corollary 2. -/
theorem KeliherSuiFiniteUpperCertificate.twoRound
    (h : KeliherSuiFiniteUpperCertificate) :
    KeliherSuiTwoRoundEstimate := by
  intro a b ha
  rw [aesIndependentSuperbox_differenceDistributionMatrix_eq_finiteCount]
  have hn : (keliherSuiSuperboxNumerator a b : ℝ) ≤
      (53 * 2 ^ 30 : Nat) := by exact_mod_cast h a b ha
  have hden : (0 : ℝ) < 256 ^ 8 := by positivity
  have hnum := div_le_div_of_nonneg_right hn (le_of_lt hden)
  have hround : ((53 * 2 ^ 30 : Nat) : ℝ) / 256 ^ 8 =
      (53 : ℝ) / 2 ^ 34 := by norm_num
  exact hnum.trans_eq hround

end PairwiseIndependence

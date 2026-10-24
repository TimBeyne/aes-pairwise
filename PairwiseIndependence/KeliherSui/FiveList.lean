import PairwiseIndependence.KeliherSui.FiniteCertificate
import Mathlib.Analysis.MeanInequalities
import PairwiseIndependence.Pairwise.SpectralWeightTwoFiber

/-!
# Keliher--Sui five-list certificate

Three fixed graph coordinates of a superbox differential leave a five-factor
sum over the MixColumns graph. A bound of `3392 = 53 · 64` on every such sum,
together with exact row and column sums of the AES difference counts for the
other three factors, gives the universal `53 / 2^34` two-round bound.
-/

namespace PairwiseIndependence

/-- Fiberwise version of the Keliher--Sui five-list reduction. A bound for
each list of five unfixed graph positions lifts to a bound on the whole
two-round trail sum, weighted by the exact totals in the three fixed
positions. The fixed values can be nonzero. -/
theorem aesMixColumn_graphProduct_le_of_fiveList_bound
    (R : Finset (Sum (Fin 4) (Fin 4)))
    (P : Sum (Fin 4) (Fin 4) → AesByte → Nat)
    (K : Nat)
    (hfive : ∀ v : R → AesByte,
      (∑ x : {x : State AesByte 4 //
          mdsGraphProjection aesMixColumnEquiv R x = v},
        ∏ j ∈ Finset.univ \ R,
          P j (mdsGraphCoordinate aesMixColumnEquiv x.1 j)) ≤ K) :
    (∑ x : State AesByte 4,
      ∏ j : Sum (Fin 4) (Fin 4),
        P j (mdsGraphCoordinate aesMixColumnEquiv x j)) ≤
      K * ∏ j : R, ∑ z : AesByte, P j.1 z := by
  classical
  let f : State AesByte 4 → Nat := fun x =>
    ∏ j : Sum (Fin 4) (Fin 4),
      P j (mdsGraphCoordinate aesMixColumnEquiv x j)
  let fixed : (R → AesByte) → Nat := fun v =>
    ∏ j : R, P j.1 (v j)
  have hsplit (v : R → AesByte)
      (x : {x : State AesByte 4 //
          mdsGraphProjection aesMixColumnEquiv R x = v}) :
      f x.1 = fixed v *
        ∏ j ∈ Finset.univ \ R,
          P j (mdsGraphCoordinate aesMixColumnEquiv x.1 j) := by
    have hfixed :
        (∏ j ∈ R,
          P j (mdsGraphCoordinate aesMixColumnEquiv x.1 j)) = fixed v := by
      rw [← Finset.prod_coe_sort R
        (fun j => P j (mdsGraphCoordinate aesMixColumnEquiv x.1 j))]
      unfold fixed
      apply Finset.prod_congr rfl
      intro j _
      have hj := congrFun x.2 j
      exact congrArg (P j.1) hj
    unfold f
    have hprod := (Finset.prod_sdiff
      (s₁ := R) (s₂ := Finset.univ)
      (f := fun j => P j (mdsGraphCoordinate aesMixColumnEquiv x.1 j))
      (Finset.subset_univ _)).symm
    rw [hprod, hfixed]
    exact mul_comm _ _
  have hbound (v : R → AesByte) :
      (∑ x : {x : State AesByte 4 //
          mdsGraphProjection aesMixColumnEquiv R x = v}, f x.1) ≤
        fixed v * K := by
    simp_rw [hsplit v]
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ (hfive v)
  have hfiber :
      (∑ x : State AesByte 4, f x) ≤
        (∑ v : R → AesByte, fixed v) * K := by
    rw [← Fintype.sum_fiberwise
      (mdsGraphProjection aesMixColumnEquiv R) f]
    calc
      _ ≤ ∑ v : R → AesByte, fixed v * K :=
        Finset.sum_le_sum (fun v _ => hbound v)
      _ = (∑ v : R → AesByte, fixed v) * K := by
        rw [Finset.sum_mul]
  have hpi :
      (∑ v : R → AesByte, fixed v) =
        ∏ j : R, ∑ z : AesByte, P j.1 z := by
    have h := Finset.sum_prod_piFinset
      (s := (Finset.univ : Finset AesByte))
      (g := fun (j : R) z => P j.1 z)
    simpa [fixed] using h
  simpa only [f, hpi, mul_comm] using hfiber

/-- Each input-difference row of the concrete AES S-box count table sums
to 256, by stochasticity of its difference-distribution matrix. -/
theorem aesSboxDifferenceCount_sum_output (a : AesByte) :
    (∑ b : AesByte, aesSboxDifferenceCount a b) = 256 := by
  have h := differenceDistributionMatrix_column_sum
    (fun _ : Unit => aesSbox) a
  change (∑ b : AesByte,
    deterministicDifferenceDistributionMatrix aesSbox b a) = 1 at h
  simp_rw [aesSbox_differenceDistributionMatrix_eq_count] at h
  change (∑ b : AesByte,
    (aesSboxDifferenceCount a b : ℝ) / 256) = 1 at h
  rw [← Finset.sum_div] at h
  have hreal : (∑ b : AesByte, (aesSboxDifferenceCount a b : ℝ)) = 256 := by
    apply (div_eq_iff (by norm_num : (256 : ℝ) ≠ 0)).mp at h
    norm_num at h ⊢
    exact h
  exact_mod_cast hreal

/-- Each output-difference column also sums to 256 because the AES S-box
is a permutation. -/
theorem aesSboxDifferenceCount_sum_input (b : AesByte) :
    (∑ a : AesByte, aesSboxDifferenceCount a b) = 256 := by
  have h := differenceDistributionMatrix_row_sum
    (fun _ : Unit => aesSbox) (fun _ => aesSboxEquiv.bijective) b
  change (∑ a : AesByte,
    deterministicDifferenceDistributionMatrix aesSbox b a) = 1 at h
  simp_rw [aesSbox_differenceDistributionMatrix_eq_count] at h
  change (∑ a : AesByte,
    (aesSboxDifferenceCount a b : ℝ) / 256) = 1 at h
  rw [← Finset.sum_div] at h
  have hreal : (∑ a : AesByte, (aesSboxDifferenceCount a b : ℝ)) = 256 := by
    apply (div_eq_iff (by norm_num : (256 : ℝ) ≠ 0)).mp at h
    norm_num at h ⊢
    exact h
  exact_mod_cast hreal

/-- One of the eight byte-count factors of a concrete two-round AES
superbox differential, indexed by its input or output graph position. -/
def aesSuperboxEndpointCount (a b : State AesByte 4) :
    Sum (Fin 4) (Fin 4) → AesByte → Nat :=
  Sum.elim
    (fun i z => aesSboxDifferenceCount (a i) z)
    (fun i z => aesSboxDifferenceCount z (b i))

/-- A uniform bound on every Keliher--Sui five-list after fixing any three
MixColumns graph coordinates. The paper's two list cases are both
represented by the arbitrary fixed values. -/
def KeliherSuiFiveListUpperCertificateAt (K : Nat) : Prop :=
  ∀ a b : State AesByte 4,
    ∀ (R : Finset (Sum (Fin 4) (Fin 4))) (_hR : R.card = 3),
    (∀ i : Fin 4, Sum.inl i ∉ R → a i ≠ 0) →
    (∀ i : Fin 4, Sum.inr i ∉ R → b i ≠ 0) →
    ∀ v : R → AesByte,
      (∑ x : {x : State AesByte 4 //
          mdsGraphProjection aesMixColumnEquiv R x = v},
        ∏ j ∈ Finset.univ \ R,
          aesSuperboxEndpointCount a b j
            (mdsGraphCoordinate aesMixColumnEquiv x.1 j)) ≤ K

/-- The search target at the paper's sharp value `3392 = 53·64` in
byte-count units, proved by `keliherSui_fiveListUpperCertificate` in
`KeliherSui/UpperBound.lean`. -/
def KeliherSuiFiveListUpperCertificate : Prop :=
  KeliherSuiFiveListUpperCertificateAt 3392

/-- A bound at any five-list threshold `K` lifts to `K·256³` on the exact
two-round superbox numerator. The proof sums the five-list estimates with
the exact totals of the three fixed byte columns. -/
theorem KeliherSuiFiveListUpperCertificateAt.numerator_le
    (K : Nat) (hcert : KeliherSuiFiveListUpperCertificateAt K)
    (a b : State AesByte 4) (ha : a ≠ 0) :
    keliherSuiSuperboxNumerator a b ≤ K * 256 ^ 3 := by
  by_cases hactivity : 5 ≤ activeCoordinates a + activeCoordinates b
  · let active : Finset (Sum (Fin 4) (Fin 4)) :=
      (Finset.univ.filter (fun i : Fin 4 => a i ≠ 0)).disjSum
        (Finset.univ.filter (fun i : Fin 4 => b i ≠ 0))
    have hacard : active.card = activeCoordinates a + activeCoordinates b := by
      simp [active, activeCoordinates, Finset.card_disjSum]
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := active) (hacard ▸ hactivity)
    let R : Finset (Sum (Fin 4) (Fin 4)) := Finset.univ \ T
    have hRcard : R.card = 3 := by
      simp [R, Finset.card_sdiff, hTcard, Fintype.card_sum]
    have houtside (j : Sum (Fin 4) (Fin 4)) (hj : j ∉ R) : j ∈ active := by
      apply hTsub
      have hjT : j ∈ T := by
        by_contra hnot
        exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hnot⟩)
      exact hjT
    have hinput (i : Fin 4) (hi : Sum.inl i ∉ R) : a i ≠ 0 := by
      simpa only [active, Finset.inl_mem_disjSum, Finset.mem_filter,
        Finset.mem_univ, true_and] using houtside (Sum.inl i) hi
    have houtput (i : Fin 4) (hi : Sum.inr i ∉ R) : b i ≠ 0 := by
      simpa only [active, Finset.inr_mem_disjSum, Finset.mem_filter,
        Finset.mem_univ, true_and] using houtside (Sum.inr i) hi
    have hfive (v : R → AesByte) :
        (∑ x : {x : State AesByte 4 //
            mdsGraphProjection aesMixColumnEquiv R x = v},
          ∏ j ∈ Finset.univ \ R,
            aesSuperboxEndpointCount a b j
              (mdsGraphCoordinate aesMixColumnEquiv x.1 j)) ≤ K :=
      hcert a b R hRcard hinput houtput v
    have hrow (j : R) :
        (∑ z : AesByte, aesSuperboxEndpointCount a b j.1 z) = 256 := by
      cases j.1 with
      | inl i => exact aesSboxDifferenceCount_sum_output (a i)
      | inr i => exact aesSboxDifferenceCount_sum_input (b i)
    have hprod :
        (∏ j : R,
          ∑ z : AesByte, aesSuperboxEndpointCount a b j.1 z) =
            256 ^ 3 := by
      simp_rw [hrow]
      simp [hRcard]
    have hgraph := aesMixColumn_graphProduct_le_of_fiveList_bound
      R (aesSuperboxEndpointCount a b) K hfive
    rw [hprod] at hgraph
    have hnum : keliherSuiSuperboxNumerator a b =
        ∑ x : State AesByte 4,
          ∏ j : Sum (Fin 4) (Fin 4),
            aesSuperboxEndpointCount a b j
              (mdsGraphCoordinate aesMixColumnEquiv x j) := by
      unfold keliherSuiSuperboxNumerator aesSuperboxEndpointCount
      simp only [Fintype.prod_sum_type, mdsGraphCoordinate,
        Sum.elim_inl, Sum.elim_inr]
    rw [hnum]
    exact hgraph
  · have hlow : activeCoordinates a + activeCoordinates b ≤ 4 := by omega
    rw [keliherSuiSuperboxNumerator_eq_zero_of_low_activity a b ha hlow]
    omega

/-- The paper's `3392` five-list search implies its universal
`53·2^30` integer numerator bound. -/
theorem KeliherSuiFiveListUpperCertificate.finiteUpper
    (hcert : KeliherSuiFiveListUpperCertificate) :
    KeliherSuiFiniteUpperCertificate := by
  intro a b ha
  have h := KeliherSuiFiveListUpperCertificateAt.numerator_le
    3392 hcert a b ha
  calc
    _ ≤ 3392 * 256 ^ 3 := h
    _ = 53 * 2 ^ 30 := by norm_num

/-- The named five-list search certificate discharges the sole numerical
premise of the concrete Corollary 2 bridge. -/
theorem KeliherSuiFiveListUpperCertificate.twoRound
    (hcert : KeliherSuiFiveListUpperCertificate) :
    KeliherSuiTwoRoundEstimate :=
  hcert.finiteUpper.twoRound

end PairwiseIndependence

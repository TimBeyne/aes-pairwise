import PairwiseIndependence.KeliherSui.LineBound
import PairwiseIndependence.AES.Equivalence
import PairwiseIndependence.KeliherSui

/-!
# Keliher--Sui's sharp two-round AES differential bound

This file closes the universal five-list certificate and exposes the
paper-facing difference-distribution matrix inequality. AES uses the
independent round keys specified by the model in the main paper.
-/

namespace PairwiseIndependence

theorem keliherSui_fiveListUpperCertificate : KeliherSuiFiveListUpperCertificate := by
  classical
  intro a b R hR ha hb v
  obtain ⟨s, hs⟩ := keliherSuiLine_cover R hR
  subst R
  obtain ⟨base, hbase⟩ := aesMixColumn_isMDS.graphProjection_surjective
    aesMixColumnEquiv (keliherSuiLineFixed s) (by omega) v
  let endpoint : Fin 5 → Fin 256 := fun i =>
    match keliherSuiLineFree s i with
    | Sum.inl j => aesByteFinEquiv.symm (a j)
    | Sum.inr j => aesByteFinEquiv.symm (b j)
  have hz : aesByteFinEquiv (0 : Fin 256) = (0 : AesByte) := by decide
  have he (i : Fin 5) : endpoint i ≠ 0 := by
    have hfree := keliherSuiLine_free_not_fixed s i
    cases hgi : keliherSuiLineFree s i with
    | inl j =>
      intro h
      apply ha j (hgi ▸ hfree)
      have h' := congrArg aesByteFinEquiv h
      simpa [endpoint, hgi, hz] using h'
    | inr j =>
      intro h
      apply hb j (hgi ▸ hfree)
      have h' := congrArg aesByteFinEquiv h
      simpa [endpoint, hgi, hz] using h'
  let e := aesByteFinEquiv.trans (keliherSuiLineFiberEquiv s v base hbase)
  have hprod (t : Fin 256) :
      (∏ j ∈ Finset.univ \ keliherSuiLineFixed s,
        aesSuperboxEndpointCount a b j
          (mdsGraphCoordinate aesMixColumnEquiv (e t).1 j)) =
      ∏ i : Fin 5, keliherSuiLineProfile s base endpoint i t := by
    rw [← (keliherSuiLine_indices s).2.2.1, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro i _
      change aesSuperboxEndpointCount a b (keliherSuiLineFree s i)
        (mdsGraphCoordinate aesMixColumnEquiv
          (base + keliherSuiLineDirection s (aesByteFinEquiv t))
          (keliherSuiLineFree s i)) = _
      rw [← keliherSuiLineCoordinate_byte]
      cases hgi : keliherSuiLineFree s i with
      | inl j =>
        simp only [aesSuperboxEndpointCount, Sum.elim_inl,
          keliherSuiLineProfile, keliherSuiLineInput, endpoint, hgi,
          ↓reduceIte]
        change aesSboxDifferenceCount (a j) _ =
          aesSboxDifferenceCount (aesByteFinEquiv (aesByteFinEquiv.symm (a j))) _
        rw [Equiv.apply_symm_apply]
        rfl
      | inr j =>
        simp only [aesSuperboxEndpointCount, Sum.elim_inr,
          keliherSuiLineProfile, keliherSuiLineInput, endpoint, hgi,
          Bool.false_eq_true, ↓reduceIte]
        change aesSboxDifferenceCount _ (b j) =
          aesSboxDifferenceCount _ (aesByteFinEquiv (aesByteFinEquiv.symm (b j)))
        rw [Equiv.apply_symm_apply]
        rfl
    · exact fun i _ j _ hij => (keliherSuiLine_indices s).2.1 hij
  have hsum :
      (∑ t : Fin 256, ∏ i : Fin 5, keliherSuiLineProfile s base endpoint i t) =
      ∑ x : {x : State AesByte 4 //
          mdsGraphProjection aesMixColumnEquiv (keliherSuiLineFixed s) x = v},
        ∏ j ∈ Finset.univ \ keliherSuiLineFixed s,
          aesSuperboxEndpointCount a b j (mdsGraphCoordinate aesMixColumnEquiv x.1 j) := by
    apply Fintype.sum_equiv e
    intro t
    exact (hprod t).symm
  rw [← hsum]
  exact keliherSuiLine_bound s base endpoint he

/-- Keliher--Sui: every nonzero input difference of the concrete AES
two-round superbox has expected differential probability at most
`53 / 2^34`. There is no remaining numerical or cryptanalytic hypothesis. -/
theorem keliherSui_twoRound_upper_bound
    (u v : State AesByte 4) (hu : u ≠ 0) :
    differenceDistributionMatrix
      (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
      v u ≤ (53 : ℝ) / (2 : ℝ) ^ 34 :=
  keliherSui_fiveListUpperCertificate.twoRound u v hu

theorem keliherSui_twoRoundEstimate : KeliherSuiTwoRoundEstimate :=
  keliherSui_twoRound_upper_bound

/-- The bound is the exact maximum, as asserted by Keliher--Sui:
every nonzero-input entry is bounded by it and the explicit witness
attains it. -/
theorem keliherSui_twoRound_exact_maximum :
    (∀ u v : State AesByte 4, u ≠ 0 →
      differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
        v u ≤ (53 : ℝ) / (2 : ℝ) ^ 34) ∧
    (∃ u v : State AesByte 4, u ≠ 0 ∧
      differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
        v u = (53 : ℝ) / (2 : ℝ) ^ 34) :=
  ⟨keliherSui_twoRound_upper_bound,
    keliherSuiWitnessInput, keliherSuiWitnessOutput,
    keliherSuiWitnessInput_ne_zero, keliherSui_twoRoundEstimate_attained⟩

/-- The Keliher–Sui bound cited in the paper; the statement is in
`KeliherSui.lean`. -/
theorem keliherSui_aesSuperbox : KeliherSuiBound := by
  unfold KeliherSuiBound
  rw [show AES.superbox = fun k c => aesIndependentSuperbox k c from
    funext₂ AES.superbox_eq]
  exact keliherSui_twoRound_exact_maximum

end PairwiseIndependence

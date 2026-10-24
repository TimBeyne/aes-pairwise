import PairwiseIndependence.AES.MixColumnsMinors

/-!
# Branch number of concrete AES MixColumns

A support-count argument combines the certified one-byte coefficients and
two-by-two minors. The inverse MixColumns coefficients handle the case of
three active input bytes. This proves the paper's byte-level MDS premise for
the standardized AES linear layer.
-/

namespace PairwiseIndependence

private def aesSupport (x : State AesByte 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => x i ≠ 0)

private theorem aesSupport_card_zero (x : State AesByte 4)
    (h : (aesSupport x).card = 0) : x = 0 := by
  have hempty : aesSupport x = ∅ := Finset.card_eq_zero.mp h
  funext i
  by_contra hi
  have hne : x i ≠ 0 := by simpa using hi
  have hmem : i ∈ aesSupport x := by simp [aesSupport, hne]
  simp [hempty] at hmem

private theorem aesSupport_not_mem (x : State AesByte 4) (i : Fin 4)
    (hi : i ∉ aesSupport x) : x i = 0 := by
  by_contra hne
  exact hi (by simp [aesSupport, hne])

private theorem aesSupport_cover_one :
    ∀ s : Finset (Fin 4), s.card ≤ 1 →
      ∃ i : Fin 4, s ⊆ {i} := by decide

private theorem aesSupport_cover_two :
    ∀ s : Finset (Fin 4), s.card ≤ 2 →
      ∃ i j : Fin 4, i ≠ j ∧ s ⊆ {i, j} := by decide

private theorem aesSupport_zero_one :
    ∀ s : Finset (Fin 4), s.card ≤ 3 →
      ∃ i : Fin 4, i ∉ s := by decide

private theorem aesSupport_zero_two :
    ∀ s : Finset (Fin 4), s.card ≤ 2 →
      ∃ i j : Fin 4, i ≠ j ∧ i ∉ s ∧ j ∉ s := by decide

private theorem aesSupport_subset_single
    (x : State AesByte 4) (i : Fin 4)
    (h : aesSupport x ⊆ {i}) :
    x = aesOneByteInput i (x i) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [aesOneByteInput]
  · have hk : k ∉ aesSupport x := by
      intro hk
      have := h hk
      simp [hki] at this
    simp [aesOneByteInput, hki, aesSupport_not_mem x k hk]

private theorem aesSupport_subset_pair
    (x : State AesByte 4) (i j : Fin 4) (hij : i ≠ j)
    (h : aesSupport x ⊆ {i, j}) :
    x = aesTwoByteInput i j (x i) (x j) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [aesTwoByteInput]
  · by_cases hkj : k = j
    · subst k
      simp [aesTwoByteInput, hij.symm]
    · have hk : k ∉ aesSupport x := by
        intro hk
        have := h hk
        simp [hki, hkj] at this
      simp [aesTwoByteInput, hki, hkj, aesSupport_not_mem x k hk]

private theorem aesMixColumn_oneByte_nonzero
    (i k : Fin 4) (a : AesByte)
    (h : aesMixColumn (aesOneByteInput i a) k = 0) : a = 0 := by
  rw [aesMixColumn_oneByteInput_apply] at h
  exact aesMixCoefficient_kernel_trivial k i a h

set_option maxHeartbeats 2000000
private def aesInvMixCoefficient (row col : Fin 4) (x : AesByte) : AesByte :=
  if row = col then aesMul14 x
  else if col = row + 1 then aesMul11 x
  else if col = row + 2 then aesMul13 x
  else aesMul9 x

private theorem aesMul9_kernel_trivial :
    ∀ x : AesByte, aesMul9 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMul11_kernel_trivial :
    ∀ x : AesByte, aesMul11 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMul13_kernel_trivial :
    ∀ x : AesByte, aesMul13 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMul14_kernel_trivial :
    ∀ x : AesByte, aesMul14 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesInvMixColumn_oneByteInput_apply
    (i k : Fin 4) (a : AesByte) :
    aesInvMixColumn (aesOneByteInput i a) k =
      aesInvMixCoefficient k i a := by
  have hxtime : aesXtime (0 : AesByte) = 0 := aesXtimeHom.map_zero
  fin_cases i <;> fin_cases k <;>
    simp [aesInvMixColumn, aesInvMixCoefficient, aesOneByteInput,
      aesMul9, aesMul11, aesMul13, aesMul14, hxtime]

private theorem aesInvMixCoefficient_kernel_trivial
    (row col : Fin 4) (a : AesByte)
    (h : aesInvMixCoefficient row col a = 0) : a = 0 := by
  unfold aesInvMixCoefficient at h
  split_ifs at h
  · exact aesMul14_kernel_trivial a h
  · exact aesMul11_kernel_trivial a h
  · exact aesMul13_kernel_trivial a h
  · exact aesMul9_kernel_trivial a h

private theorem aesInvMixColumn_oneByte_nonzero :
    ∀ i k : Fin 4, ∀ a : AesByte,
      aesInvMixColumn (aesOneByteInput i a) k = 0 → a = 0 := by
  intro i k a h
  rw [aesInvMixColumn_oneByteInput_apply] at h
  exact aesInvMixCoefficient_kernel_trivial k i a h

private theorem aesInvMixColumn_zero :
    aesInvMixColumn (0 : State AesByte 4) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The concrete FIPS 197 MixColumns layer has branch number five. -/
theorem aesMixColumn_isMDS : IsMDS aesMixColumnEquiv := by
  intro x hx
  let y := aesMixColumn x
  let sx := aesSupport x
  let sy := aesSupport y
  have hxpos : 0 < sx.card := by
    by_cases hzero : sx.card = 0
    · exact False.elim (hx (aesSupport_card_zero x hzero))
    · exact Nat.pos_of_ne_zero hzero
  have hypos : 0 < sy.card := by
    by_cases hzero : sy.card = 0
    · have hyzero : y = 0 := aesSupport_card_zero y hzero
      have hxzero : x = 0 := by
        calc
          x = aesInvMixColumn y := (aesInvMixColumn_mix x).symm
          _ = 0 := by rw [hyzero]; exact aesInvMixColumn_zero
      exact False.elim (hx hxzero)
    · exact Nat.pos_of_ne_zero hzero
  by_contra hbranch
  have hsum : sx.card + sy.card ≤ 4 := by
    change ¬ 5 ≤ sx.card + sy.card at hbranch
    omega
  by_cases hxone : sx.card ≤ 1
  · obtain ⟨i, hi⟩ := aesSupport_cover_one sx hxone
    have hrep : x = aesOneByteInput i (x i) := aesSupport_subset_single x i hi
    obtain ⟨k, hk⟩ := aesSupport_zero_one sy (by omega)
    have hyk : y k = 0 := aesSupport_not_mem y k hk
    have hcol : aesMixColumn (aesOneByteInput i (x i)) k = 0 := by
      change aesMixColumn x k = 0 at hyk
      rwa [hrep] at hyk
    have hxi : x i = 0 := aesMixColumn_oneByte_nonzero i k (x i) hcol
    have hinput : aesOneByteInput i (x i) = 0 := by
      rw [hxi]
      funext r
      simp [aesOneByteInput]
    exact hx (hrep.trans hinput)
  by_cases hxtwo : sx.card ≤ 2
  · obtain ⟨i, j, hij, hi⟩ := aesSupport_cover_two sx hxtwo
    have hrep : x = aesTwoByteInput i j (x i) (x j) :=
      aesSupport_subset_pair x i j hij hi
    obtain ⟨k, l, hkl, hk, hl⟩ := aesSupport_zero_two sy (by omega)
    have hyk : y k = 0 := aesSupport_not_mem y k hk
    have hyl : y l = 0 := aesSupport_not_mem y l hl
    change aesMixColumn x k = 0 at hyk
    change aesMixColumn x l = 0 at hyl
    rw [hrep] at hyk hyl
    have hab := aesMixColumn_twoByte_minor i j k l hij hkl (x i) (x j)
      hyk hyl
    have hinput : aesTwoByteInput i j (x i) (x j) = 0 := by
      rw [hab.1, hab.2]
      funext r
      simp [aesTwoByteInput]
    exact hx (hrep.trans hinput)
  have hyone : sy.card ≤ 1 := by omega
  obtain ⟨j, hj⟩ := aesSupport_cover_one sy hyone
  have hyrep : y = aesOneByteInput j (y j) := aesSupport_subset_single y j hj
  obtain ⟨k, hk⟩ := aesSupport_zero_one sx (by omega)
  have hxk : x k = 0 := aesSupport_not_mem x k hk
  have hinv : aesInvMixColumn y = x := aesInvMixColumn_mix x
  have hEq := congrArg (fun z : State AesByte 4 => aesInvMixColumn z k) hyrep
  have hinvcol : aesInvMixColumn (aesOneByteInput j (y j)) k = 0 := by
    calc
      aesInvMixColumn (aesOneByteInput j (y j)) k = aesInvMixColumn y k := hEq.symm
      _ = x k := congrFun hinv k
      _ = 0 := hxk
  have hval : y j = 0 := aesInvMixColumn_oneByte_nonzero j k (y j) hinvcol
  have hinput : aesOneByteInput j (y j) = 0 := by
    rw [hval]
    funext r
    simp [aesOneByteInput]
  have hyzero : y = 0 := hyrep.trans hinput
  exact hx (by
    calc
      x = aesInvMixColumn y := hinv.symm
      _ = 0 := by rw [hyzero]; exact aesInvMixColumn_zero)

end PairwiseIndependence

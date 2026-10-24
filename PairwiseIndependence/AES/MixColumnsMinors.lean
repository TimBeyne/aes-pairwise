import PairwiseIndependence.AES.Byte

/-!
# AES MixColumns minor certificates

The coefficients are the FIPS 197 multipliers `01`, `02`, and `03`.
Lean checks the finite byte kernels of the coefficients, classifies every
two-by-two minor determinant symbolically as one of six byte polynomials, and
checks the needed polynomial kernels. Additive equations then prove the actual
restricted MixColumns maps have trivial kernel. The finite certificates use
ordinary kernel-checked `decide`, not native evaluation.
-/

namespace PairwiseIndependence

def aesMixCoefficient (row col : Fin 4) (x : AesByte) : AesByte :=
  if row = col then aesXtime x
  else if col = row + 1 then aesMul3 x
  else x

theorem aesMixCoefficient_add (row col : Fin 4) (x y : AesByte) :
    aesMixCoefficient row col (x + y) =
      aesMixCoefficient row col x + aesMixCoefficient row col y := by
  unfold aesMixCoefficient
  split_ifs <;> simp [aesXtime_add, aesMul3_add]

theorem aesMixCoefficient_zero (row col : Fin 4) :
    aesMixCoefficient row col 0 = 0 := by
  unfold aesMixCoefficient
  split_ifs
  · exact aesXtimeHom.map_zero
  · simp [aesMul3, show aesXtime 0 = 0 from aesXtimeHom.map_zero]
  · rfl

theorem aesXtime_mul3_commute (x : AesByte) :
    aesXtime (aesMul3 x) = aesMul3 (aesXtime x) := by
  simp [aesMul3, aesXtime_add]

theorem aesMixCoefficient_commute (r c s d : Fin 4) (x : AesByte) :
    aesMixCoefficient r c (aesMixCoefficient s d x) =
      aesMixCoefficient s d (aesMixCoefficient r c x) := by
  unfold aesMixCoefficient
  split_ifs <;> simp [aesXtime_mul3_commute]

theorem aesMixCoefficient_kernel_trivial :
    ∀ r c : Fin 4, ∀ x : AesByte,
      aesMixCoefficient r c x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private def aesMinorPolynomial7 (x : AesByte) : AesByte :=
  x + aesXtime x + aesXtime (aesXtime x)

private theorem aesByte_two_eq_zero : (2 : AesByte) = 0 := by
  funext i
  change (2 : ZMod 2) = 0
  decide

private theorem aesByte_three_eq_one : (3 : AesByte) = 1 := by
  funext i
  change (3 : ZMod 2) = 1
  decide

attribute [local simp] aesByte_two_eq_zero aesByte_three_eq_one

private theorem aesMinorPolynomial2_kernel_trivial :
    ∀ x : AesByte, aesXtime x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMinorPolynomial4_kernel_trivial :
    ∀ x : AesByte, aesXtime (aesXtime x) = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMinorPolynomial5_kernel_trivial :
    ∀ x : AesByte, aesMul3 (aesMul3 x) = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

private theorem aesMinorPolynomial7_kernel_trivial :
    ∀ x : AesByte, aesMinorPolynomial7 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in decide

set_option maxHeartbeats 2000000
/-- Every distinct-row, distinct-column MixColumns minor is one of six
polynomial multipliers: `01`, `02`, `03`, `04`, `05`, or `07`. This is a
symbolic, finite check of the 4×4 coefficient matrix. -/
private theorem aesMixMinorDeterminant_shape
    (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) (x : AesByte) :
    let d := aesMixCoefficient l j (aesMixCoefficient k i x) +
      aesMixCoefficient k j (aesMixCoefficient l i x)
    d = x ∨ d = aesXtime x ∨ d = aesMul3 x ∨
      d = aesXtime (aesXtime x) ∨
      d = aesMul3 (aesMul3 x) ∨ d = aesMinorPolynomial7 x := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [aesMixCoefficient, aesMul3, aesMinorPolynomial7,
      aesXtime_add] <;>
    solve
    | left; ring_nf; simp
    | right; left; ring_nf; simp
    | right; right; left; ring_nf <;> simp
    | right; right; right; left; ring_nf; simp
    | right; right; right; right; left; ring_nf; simp
    | right; right; right; right; right; ring_nf <;> simp

theorem aesMixMinorDeterminant_kernel_trivial :
    ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
      ∀ x : AesByte,
        aesMixCoefficient l j (aesMixCoefficient k i x) +
          aesMixCoefficient k j (aesMixCoefficient l i x) = 0 →
        x = 0 := by
  intro i j k l hij hkl x hzero
  rcases aesMixMinorDeterminant_shape i j k l hij hkl x with
    h | h | h | h | h | h
  · exact h.symm.trans hzero
  · exact aesMinorPolynomial2_kernel_trivial x (h.symm.trans hzero)
  · exact aesMul3_kernel_trivial x (h.symm.trans hzero)
  · exact aesMinorPolynomial4_kernel_trivial x (h.symm.trans hzero)
  · exact aesMinorPolynomial5_kernel_trivial x (h.symm.trans hzero)
  · exact aesMinorPolynomial7_kernel_trivial x (h.symm.trans hzero)

def aesTwoByteInput (i j : Fin 4) (a b : AesByte) : State AesByte 4 :=
  fun r => if r = i then a else if r = j then b else 0

def aesOneByteInput (i : Fin 4) (a : AesByte) : State AesByte 4 :=
  fun r => if r = i then a else 0

theorem aesMixColumn_oneByteInput_apply (i k : Fin 4) (a : AesByte) :
    aesMixColumn (aesOneByteInput i a) k = aesMixCoefficient k i a := by
  have hxtime : aesXtime (0 : AesByte) = 0 := aesXtimeHom.map_zero
  fin_cases i <;> fin_cases k <;>
    simp [aesOneByteInput, aesMixColumn, aesMixCoefficient, aesMul3,
      hxtime, add_comm]

theorem aesTwoByteInput_eq_add
    (i j : Fin 4) (hij : i ≠ j) (a b : AesByte) :
    aesTwoByteInput i j a b = aesOneByteInput i a + aesOneByteInput j b := by
  funext r
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [aesTwoByteInput, aesOneByteInput, Pi.add_apply]

theorem aesMixColumn_twoByteInput_apply
    (i j k : Fin 4) (hij : i ≠ j) (a b : AesByte) :
    aesMixColumn (aesTwoByteInput i j a b) k =
      aesMixCoefficient k i a + aesMixCoefficient k j b := by
  rw [aesTwoByteInput_eq_add i j hij, aesMixColumn_add]
  exact congrArg₂ (· + ·)
    (aesMixColumn_oneByteInput_apply i k a)
    (aesMixColumn_oneByteInput_apply j k b)

private theorem aesByte_add_self_eq_zero' (x : AesByte) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem aesByte_eq_of_add_eq_zero' (x y : AesByte)
    (h : x + y = 0) : x = y := by
  calc
    x = x + (y + y) := by rw [aesByte_add_self_eq_zero', add_zero]
    _ = (x + y) + y := by ac_rfl
    _ = y := by rw [h, zero_add]

/-- Any two zero outputs of a two-byte input force both inputs to be zero. -/
theorem aesMixColumn_twoByte_minor
    (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
    (a b : AesByte)
    (hk : aesMixColumn (aesTwoByteInput i j a b) k = 0)
    (hl : aesMixColumn (aesTwoByteInput i j a b) l = 0) :
    a = 0 ∧ b = 0 := by
  have h₁ : aesMixCoefficient k i a + aesMixCoefficient k j b = 0 := by
    simpa only [aesMixColumn_twoByteInput_apply i j k hij] using hk
  have h₂ : aesMixCoefficient l i a + aesMixCoefficient l j b = 0 := by
    simpa only [aesMixColumn_twoByteInput_apply i j l hij] using hl
  have h₁' := congrArg (aesMixCoefficient l j) h₁
  rw [aesMixCoefficient_add, aesMixCoefficient_zero] at h₁'
  have h₂' := congrArg (aesMixCoefficient k j) h₂
  rw [aesMixCoefficient_add, aesMixCoefficient_zero] at h₂'
  have hcomm := aesMixCoefficient_commute l j k j b
  have hp := aesByte_eq_of_add_eq_zero' _ _ h₁'
  have hq := aesByte_eq_of_add_eq_zero' _ _ h₂'
  have hdet :
      aesMixCoefficient l j (aesMixCoefficient k i a) +
        aesMixCoefficient k j (aesMixCoefficient l i a) = 0 := by
    rw [hp, hq, ← hcomm]
    exact aesByte_add_self_eq_zero' _
  have ha := aesMixMinorDeterminant_kernel_trivial i j k l hij hkl a hdet
  have hbzero : aesMixCoefficient k j b = 0 := by
    simpa [ha, aesMixCoefficient_zero] using h₁
  exact ⟨ha, aesMixCoefficient_kernel_trivial k j b hbzero⟩
end PairwiseIndependence

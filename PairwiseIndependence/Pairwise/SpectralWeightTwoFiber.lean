import PairwiseIndependence.Pairwise.Spectral

/-!
# The one-dimensional fiber calculation in Remark 1

For total spectral weight two, the paper's MDS graph fiber has one free
nonzero coordinate. The generic absolute-value estimate loses a factor of
about two. This file proves the exact `q - 2` calculation for a permutation
of that coordinate, using the same complementary-basis kernel as Lemma 13.
-/

namespace PairwiseIndependence

open scoped Matrix




private theorem sum_eq_subtype_of_zero_outside
    {F : Type*} [Fintype F] [DecidableEq F]
    (P : F → Prop) [DecidablePred P]
    (f : F → ℝ) (hf : ∀ x, ¬P x → f x = 0) :
    (∑ x : F, f x) = ∑ x : {x : F // P x}, f x.1 := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype P f
  have hsecond :
      (∑ x : {x : F // ¬P x}, f x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hf x.1 x.2
  rw [hsecond, add_zero] at h
  exact h.symm

private theorem double_sum_eq_subtype_of_zero_outside
    {F : Type*} [Fintype F] [DecidableEq F]
    (P : F → Prop) [DecidablePred P]
    (g : F → F → ℝ)
    (hrow : ∀ x, ¬P x → ∀ y, g x y = 0)
    (hcol : ∀ y, ¬P y → ∀ x, g x y = 0) :
    (∑ x : F, ∑ y : F, g x y) =
      ∑ x : {x : F // P x},
        ∑ y : {y : F // P y}, g x.1 y.1 := by
  calc
    (∑ x : F, ∑ y : F, g x y) =
        ∑ x : {x : F // P x}, ∑ y : F, g x.1 y := by
      apply sum_eq_subtype_of_zero_outside P
      intro x hx
      simp [hrow x hx]
    _ = ∑ x : {x : F // P x},
          ∑ y : {y : F // P y}, g x.1 y.1 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_eq_subtype_of_zero_outside P (g x.1)
        (fun y hy => hcol y hy x.1)

/-- On a graph-code fiber with `n-1` zero coordinates, any additional
coordinate uniquely determines the codeword. This is the paper's one-free-
coordinate parametrization for the `l=2` case. -/
noncomputable def mdsGraphZeroFiberCoordinateEquiv
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j : Sum (Fin n) (Fin n)) (hj : j ∉ Z) :
    {a : State A n // mdsGraphProjection L Z a = 0} ≃ A := by
  classical
  let F := {a : State A n // mdsGraphProjection L Z a = 0}
  let s := insert j Z
  have hs : s.card = n := by
    simp [s, Finset.card_insert_of_notMem hj, hZ]
  let f : F → A := fun a => mdsGraphCoordinate L a.1 j
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hMDS.graphProjection_injective L s (by omega)
    funext i
    rcases Finset.mem_insert.mp i.2 with hij | hiZ
    · change mdsGraphCoordinate L a.1 i.1 =
          mdsGraphCoordinate L b.1 i.1
      simpa only [hij, f] using hab
    · have ha := congrFun a.2 ⟨i.1, hiZ⟩
      have hb := congrFun b.2 ⟨i.1, hiZ⟩
      change mdsGraphCoordinate L a.1 i.1 = 0 at ha
      change mdsGraphCoordinate L b.1 i.1 = 0 at hb
      exact ha.trans hb.symm
  have hf_surj : Function.Surjective f := by
    intro b
    let target : s → A := fun i => if i.1 = j then b else 0
    obtain ⟨a, ha⟩ := (hMDS.graphProjection_bijective L s hs).2 target
    have haZ : mdsGraphProjection L Z a = 0 := by
      funext i
      let hi : s := ⟨i.1, Finset.mem_insert_of_mem i.2⟩
      have hai := congrFun ha hi
      have hij : i.1 ≠ j := by
        intro heq
        exact hj (heq ▸ i.2)
      change mdsGraphCoordinate L a i.1 =
        (if i.1 = j then b else 0) at hai
      simpa only [mdsGraphProjection, if_neg hij] using hai
    have haj := congrFun ha (⟨j, Finset.mem_insert_self j Z⟩ : s)
    refine ⟨⟨a, haZ⟩, ?_⟩
    simpa [f, mdsGraphProjection, target] using haj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- The coordinate parametrization sends the zero graph codeword to zero. -/
theorem mdsGraphZeroFiberCoordinateEquiv_zero
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j : Sum (Fin n) (Fin n)) (hj : j ∉ Z) :
    mdsGraphZeroFiberCoordinateEquiv L hMDS Z hZ j hj
      ⟨0, by simp⟩ = 0 := by
  simp [mdsGraphZeroFiberCoordinateEquiv, mdsGraphCoordinate]

/-- A nonzero codeword in the one-dimensional zero fiber has a nonzero
value at every graph coordinate outside the fixed zero set. -/
theorem mdsGraphZeroFiberCoordinate_ne_zero
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j : Sum (Fin n) (Fin n)) (hj : j ∉ Z)
    (a : {a : State A n // mdsGraphProjection L Z a = 0})
    (ha : a.1 ≠ 0) : mdsGraphCoordinate L a.1 j ≠ 0 := by
  intro hzero
  let e := mdsGraphZeroFiberCoordinateEquiv L hMDS Z hZ j hj
  have hbase : e (⟨0, by simp⟩ :
      {a : State A n // mdsGraphProjection L Z a = 0}) = 0 :=
    mdsGraphZeroFiberCoordinateEquiv_zero L hMDS Z hZ j hj
  have hea : e a = 0 := by
    simpa only [e, mdsGraphZeroFiberCoordinateEquiv] using hzero
  have heq : e a = e ⟨0, by simp⟩ := hea.trans hbase.symm
  exact ha (congrArg Subtype.val (e.injective heq))

/-- The paper's nonzero one-dimensional graph fiber can be indexed by
nonzero values of any coordinate outside the fixed zero positions. -/
noncomputable def mdsGraphZeroFiberNonzeroCoordinateEquiv
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j : Sum (Fin n) (Fin n)) (hj : j ∉ Z) :
    {a : {a : State A n // mdsGraphProjection L Z a = 0} // a.1 ≠ 0} ≃
      {b : A // b ≠ 0} :=
  (mdsGraphZeroFiberCoordinateEquiv L hMDS Z hZ j hj).subtypeEquiv
    (by
      intro a
      constructor
      · exact mdsGraphZeroFiberCoordinate_ne_zero L hMDS Z hZ j hj a
      · intro he ha
        have hzero : a = ⟨0, by simp⟩ := Subtype.ext ha
        apply he
        rw [hzero]
        exact mdsGraphZeroFiberCoordinateEquiv_zero L hMDS Z hZ j hj)

private theorem indicator_square_sum
    (B : Type*) [Fintype B] [DecidableEq B] (c : ℝ) :
    (∑ x : B, ∑ y : B, ((if x = y then (1 : ℝ) else 0) - c) ^ 2) =
      (Fintype.card B : ℝ) *
        (1 - 2 * c + (Fintype.card B : ℝ) * c ^ 2) := by
  have hpoint (x y : B) :
      ((if x = y then (1 : ℝ) else 0) - c) ^ 2 =
        (if x = y then (1 : ℝ) else 0) * (1 - 2 * c) + c ^ 2 := by
    split_ifs <;> ring
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib, mul_add]

/-- Remark 1's exact `q - 2` kernel sum on a one-dimensional nonzero
fiber. Any bijective change of the free coordinate gives the same sum. -/
theorem spectralWeightTwo_nonzeroFiber_kernel_sum
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (hcard : 3 ≤ Fintype.card A)
    (p : {a : A // a ≠ 0} ≃ {a : A // a ≠ 0}) :
    (∑ x : {a : A // a ≠ 0},
      ∑ y : {a : A // a ≠ 0},
        wordComplementBasisKernel (A := A) x.1 y.1 *
          wordComplementBasisKernel (A := A) (p x).1 (p y).1) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  let B := {a : A // a ≠ 0}
  have hBnat : Fintype.card B = Fintype.card A - 1 := by
    simpa only [B] using
      (Fintype.card_subtype_compl (fun a : A => a = 0))
  have hB : (Fintype.card B : ℝ) = (Fintype.card A : ℝ) - 1 := by
    rw [hBnat]
    have hpos : 1 ≤ Fintype.card A := by omega
    rw [Nat.cast_sub hpos]
    norm_num
  let c : ℝ := (Fintype.card B : ℝ)⁻¹
  have hBpos : (0 : ℝ) < Fintype.card B := by
    rw [hB]
    have hreal : (3 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
    linarith
  have hk (x y : B) :
      wordComplementBasisKernel (A := A) x.1 y.1 =
        (if x = y then (1 : ℝ) else 0) - c := by
    rw [wordComplementBasisKernel_nonzero x.1 y.1 x.2 y.2]
    rw [← hB]
    have hxy : (x.1 = y.1) ↔ x = y := Subtype.coe_inj
    simp only [hxy, c]
  calc
    (∑ x : B, ∑ y : B,
      wordComplementBasisKernel (A := A) x.1 y.1 *
        wordComplementBasisKernel (A := A) (p x).1 (p y).1) =
      ∑ x : B, ∑ y : B, ((if x = y then (1 : ℝ) else 0) - c) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [hk x y, hk (p x) (p y)]
        have hp : (p x = p y) ↔ x = y := p.injective.eq_iff
        simp only [hp]
        ring
    _ = (Fintype.card B : ℝ) *
        (1 - 2 * c + (Fintype.card B : ℝ) * c ^ 2) :=
      indicator_square_sum B c
    _ = (Fintype.card A : ℝ) - 2 := by
      dsimp [c]
      field_simp
      rw [hB]
      ring

/-- The same `q−2` identity when the one-dimensional nonzero fiber is
parametrized by two different graph coordinates. -/
theorem spectralWeightTwo_nonzeroFiber_kernel_sum_of_equivs
    {A F : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype F] [DecidableEq F]
    (hcard : 3 ≤ Fintype.card A)
    (e₁ e₂ : F ≃ {a : A // a ≠ 0}) :
    (∑ x : F, ∑ y : F,
      wordComplementBasisKernel (A := A) (e₁ x).1 (e₁ y).1 *
        wordComplementBasisKernel (A := A) (e₂ x).1 (e₂ y).1) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  let B := {a : A // a ≠ 0}
  let p : B ≃ B := e₁.symm.trans e₂
  let f (x y : F) : ℝ :=
    wordComplementBasisKernel (A := A) (e₁ x).1 (e₁ y).1 *
      wordComplementBasisKernel (A := A) (e₂ x).1 (e₂ y).1
  change (∑ x : F, ∑ y : F, f x y) = _
  calc
    (∑ x : F, ∑ y : F, f x y) =
        ∑ x : B, ∑ y : F, f (e₁.symm x) y := by
      symm
      exact e₁.symm.sum_comp (fun x : F => ∑ y : F, f x y)
    _ = ∑ x : B, ∑ y : B, f (e₁.symm x) (e₁.symm y) := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      exact e₁.symm.sum_comp (fun y : F => f (e₁.symm x) y)
    _ = ∑ x : B, ∑ y : B,
        wordComplementBasisKernel (A := A) x.1 y.1 *
          wordComplementBasisKernel (A := A) (p x).1 (p y).1 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      simp only [f, p, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    _ = (Fintype.card A : ℝ) - 2 :=
      spectralWeightTwo_nonzeroFiber_kernel_sum hcard p

/-- Remark 1's `q−2` double sum on the actual nonzero MDS graph fiber,
for any two complementary coordinates outside the `n−1` zero positions. -/
theorem IsMDS.graphZeroFiber_twoComplementKernels_nonzero_sum_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j₁ j₂ : Sum (Fin n) (Fin n))
    (hj₁ : j₁ ∉ Z) (hj₂ : j₂ ∉ Z) :
    (∑ a : {a : {a : State A n // mdsGraphProjection L Z a = 0} // a.1 ≠ 0},
      ∑ b : {a : {a : State A n // mdsGraphProjection L Z a = 0} // a.1 ≠ 0},
        wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a.1.1 j₁)
            (mdsGraphCoordinate L b.1.1 j₁) *
          wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a.1.1 j₂)
            (mdsGraphCoordinate L b.1.1 j₂)) =
      (Fintype.card A : ℝ) - 2 := by
  let e₁ := mdsGraphZeroFiberNonzeroCoordinateEquiv L hMDS Z hZ j₁ hj₁
  let e₂ := mdsGraphZeroFiberNonzeroCoordinateEquiv L hMDS Z hZ j₂ hj₂
  have h := spectralWeightTwo_nonzeroFiber_kernel_sum_of_equivs hcard e₁ e₂
  exact h

/-- The exact `q−2` result for the full one-dimensional MDS graph fiber.
The zero codeword contributes zero because every complementary-basis kernel
vanishes when either argument is zero. -/
theorem IsMDS.graphZeroFiber_twoComplementKernels_sum_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j₁ j₂ : Sum (Fin n) (Fin n))
    (hj₁ : j₁ ∉ Z) (hj₂ : j₂ ∉ Z) :
    (∑ a : {a : State A n // mdsGraphProjection L Z a = 0},
      ∑ b : {a : State A n // mdsGraphProjection L Z a = 0},
        wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a.1 j₁)
            (mdsGraphCoordinate L b.1 j₁) *
          wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a.1 j₂)
            (mdsGraphCoordinate L b.1 j₂)) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  let F := {a : State A n // mdsGraphProjection L Z a = 0}
  let P : F → Prop := fun a => a.1 ≠ 0
  let g (a b : F) : ℝ :=
    wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a.1 j₁) (mdsGraphCoordinate L b.1 j₁) *
      wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a.1 j₂) (mdsGraphCoordinate L b.1 j₂)
  have hrow : ∀ a : F, ¬P a → ∀ b : F, g a b = 0 := by
    intro a ha b
    have ha0 : a.1 = 0 := not_not.mp ha
    simp [g, ha0, mdsGraphCoordinate, wordComplementBasisKernel_zero_left]
  have hcol : ∀ b : F, ¬P b → ∀ a : F, g a b = 0 := by
    intro b hb a
    have hb0 : b.1 = 0 := not_not.mp hb
    simp [g, hb0, mdsGraphCoordinate, wordComplementBasisKernel_zero_right]
  change (∑ a : F, ∑ b : F, g a b) = _
  calc
    (∑ a : F, ∑ b : F, g a b) =
        ∑ a : {a : F // P a}, ∑ b : {b : F // P b}, g a.1 b.1 :=
      double_sum_eq_subtype_of_zero_outside P g hrow hcol
    _ = (Fintype.card A : ℝ) - 2 :=
      hMDS.graphZeroFiber_twoComplementKernels_nonzero_sum_eq
        L hcard Z hZ j₁ j₂ hj₁ hj₂

/-- Remark 1's exact replacement for the generic MDS graph-fiber
absolute-value estimate when the complementary-position set has size two. -/
theorem IsMDS.graphZeroFiber_twoComplementPositions_sum_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j₁ j₂ : Sum (Fin n) (Fin n))
    (hj₁ : j₁ ∉ Z) (hj₂ : j₂ ∉ Z) (hjne : j₁ ≠ j₂) :
    (∑ a : {a : State A n // mdsGraphProjection L Z a = 0},
      ∑ b : {a : State A n // mdsGraphProjection L Z a = 0},
        ∏ i : ({j₁, j₂} : Finset (Sum (Fin n) (Fin n))),
          wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a.1 i.1)
            (mdsGraphCoordinate L b.1 i.1)) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  have hprod (a b : {a : State A n // mdsGraphProjection L Z a = 0}) :
      (∏ i : ({j₁, j₂} : Finset (Sum (Fin n) (Fin n))),
        wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a.1 i.1)
          (mdsGraphCoordinate L b.1 i.1)) =
        wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a.1 j₁)
          (mdsGraphCoordinate L b.1 j₁) *
        wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a.1 j₂)
          (mdsGraphCoordinate L b.1 j₂) := by
    let I : Finset (Sum (Fin n) (Fin n)) := {j₁, j₂}
    let k (i : Sum (Fin n) (Fin n)) : ℝ :=
      wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a.1 i)
        (mdsGraphCoordinate L b.1 i)
    change (∏ i : I, k i.1) = k j₁ * k j₂
    calc
      (∏ i : I, k i.1) = ∏ i ∈ I, k i :=
        Finset.prod_coe_sort I k
      _ = k j₁ * k j₂ := by simp [I, hjne]
  simp_rw [hprod]
  exact hMDS.graphZeroFiber_twoComplementKernels_sum_eq
    L hcard Z hZ j₁ j₂ hj₁ hj₂

/-- Remark 1 in the zero-fiber notation used by the spectral matrix proof. -/
theorem IsMDS.graphZeroFiber_twoComplementPositions_finset_sum_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (Z : Finset (Sum (Fin n) (Fin n))) (hZ : Z.card + 1 = n)
    (j₁ j₂ : Sum (Fin n) (Fin n))
    (hj₁ : j₁ ∉ Z) (hj₂ : j₂ ∉ Z) (hjne : j₁ ≠ j₂) :
    (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
      ∑ b ∈ (Finset.univ.filter (fun b : State A n =>
          mdsGraphProjection L Z b = 0)),
        ∏ i : ({j₁, j₂} : Finset (Sum (Fin n) (Fin n))),
          wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a i.1)
            (mdsGraphCoordinate L b i.1)) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  let C : Finset (State A n) :=
    Finset.univ.filter (fun a => mdsGraphProjection L Z a = 0)
  let F := {a : State A n // mdsGraphProjection L Z a = 0}
  let I : Finset (Sum (Fin n) (Fin n)) := {j₁, j₂}
  let k (a b : State A n) : ℝ :=
    ∏ i : I, wordComplementBasisKernel (A := A)
      (mdsGraphCoordinate L a i.1) (mdsGraphCoordinate L b i.1)
  have hsum (f : State A n → ℝ) :
      (∑ a ∈ C, f a) = ∑ a : F, f a.1 := by
    simpa only [C, F, Finset.subtype_univ,
      Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.sum_subtype_eq_sum_filter
        (s := Finset.univ)
        (p := fun a : State A n => mdsGraphProjection L Z a = 0) f).symm
  change (∑ a ∈ C, ∑ b ∈ C, k a b) = _
  calc
    (∑ a ∈ C, ∑ b ∈ C, k a b) =
        ∑ a : F, ∑ b ∈ C, k a.1 b := hsum _
    _ = ∑ a : F, ∑ b : F, k a.1 b.1 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hsum _
    _ = (Fintype.card A : ℝ) - 2 :=
      hMDS.graphZeroFiber_twoComplementPositions_sum_eq
        L hcard Z hZ j₁ j₂ hj₁ hj₂ hjne

/-- Remark 1's improved MDS estimate at total spectral weight two,
before the paper counts complementary-position choices. Unlike the generic
bound, this is an equality for the sum of squared basis coefficients. -/
theorem IsMDS.graphZeroFiber_complementBasis_sum_squares_eq_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (Z I : Finset (Sum (Fin n) (Fin n)))
    (hZ : Z.card + 1 = n) (hI : I.card = 2)
    (hdisj : Disjoint Z I) :
    (∑ j : (I → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
        ∏ i : I, wordComplementBasisVector (A := A) (j i)
          (mdsGraphCoordinate L a i.1)) ^ 2) =
      (Fintype.card A : ℝ) - 2 := by
  classical
  obtain ⟨j₁, j₂, hjne, rfl⟩ := Finset.card_eq_two.mp hI
  have hj₁ : j₁ ∉ Z := by
    intro hmem
    exact (Finset.disjoint_left.mp hdisj) hmem (by simp)
  have hj₂ : j₂ ∉ Z := by
    intro hmem
    exact (Finset.disjoint_left.mp hdisj) hmem (by simp)
  let C : Finset (State A n) := Finset.univ.filter
    (fun a => mdsGraphProjection L Z a = 0)
  let I : Finset (Sum (Fin n) (Fin n)) := {j₁, j₂}
  have hexact := wordComplementBasisKernel_sum_squares_finite
    (A := A) (J := I) C (fun a i => mdsGraphCoordinate L a i.1)
  calc
    (∑ j : (I → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      (∑ a ∈ C, ∏ i : I, wordComplementBasisVector (A := A) (j i)
        (mdsGraphCoordinate L a i.1)) ^ 2) =
      ∑ a ∈ C, ∑ b ∈ C, ∏ i : I,
        wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a i.1)
          (mdsGraphCoordinate L b i.1) := hexact
    _ = (Fintype.card A : ℝ) - 2 :=
      hMDS.graphZeroFiber_twoComplementPositions_finset_sum_eq
        L hcard Z hZ j₁ j₂ hj₁ hj₂ hjne

/-- The paper's fixed-position Frobenius identity at total spectral weight
two, with its exact `q−2` factor and the unchanged normalized all-indicator
factor. This replaces the generic `2(q−1)` fiber estimate in Remark 1. -/
theorem IsMDS.spectralBasisMatrix_fixedActivity_sum_squares_eq_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hZ : (spectralBasisGraphZeroPositions l₁ l₂ c d).card + 1 = n)
    (hI : (spectralBasisGraphComplementPositions l₁ l₂ c d).card = 2) :
    let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
    let I := spectralBasisGraphComplementPositions l₁ l₂ c d
    let α : ℝ := ((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
      ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card
    (∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁ c f)
            (spectralBasisIndex_withComplementChoices l₂ d g)) ^ 2)) =
      α ^ 2 * ((Fintype.card A : ℝ) - 2) := by
  have hbase := spectralBasisMatrix_fixedActivity_sum_squares_eq L l₁ l₂ c d
  dsimp only at hbase ⊢
  rw [hbase]
  rw [hMDS.graphZeroFiber_complementBasis_sum_squares_eq_weightTwo
    L hcard _ _ hZ hI
      (spectralBasisGraphZeroPositions_disjoint_complementPositions
        l₁ l₂ c d)]

/-- The same exact fixed-position identity in the paper's `q`-power
normalization, ready for the Frobenius sum over position choices. -/
theorem IsMDS.spectralBasisMatrix_fixedActivity_sum_squares_eq_weightTwo_normalized
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hZ : (spectralBasisGraphZeroPositions l₁ l₂ c d).card + 1 = n)
    (hI : (spectralBasisGraphComplementPositions l₁ l₂ c d).card = 2) :
    let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
    (∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁ c f)
            (spectralBasisIndex_withComplementChoices l₂ d g)) ^ 2)) =
      ((Fintype.card A : ℝ)⁻¹) ^
        (2 * n - Z.card - (l₁ + l₂)) *
          ((Fintype.card A : ℝ) - 2) := by
  have hb := hMDS.spectralBasisMatrix_fixedActivity_sum_squares_eq_weightTwo
    L hcard l₁ l₂ c d hZ hI
  have hc := spectralBasisGraphUniformPositions_card l₁ l₂ c d
  dsimp only at hb hc ⊢
  rw [hc] at hb
  rw [normalizedAllIndicatorFactor_sq] at hb
  exact hb

end PairwiseIndependence

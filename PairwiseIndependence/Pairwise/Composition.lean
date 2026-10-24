import PairwiseIndependence.Pairwise.DifferenceDistribution

/-!
# Composing difference-distribution matrices

A fresh uniform intermediate key makes the difference after the first function
uniformly positioned at the input of the second function. This is the precise
reason the paper can multiply difference-distribution matrices.
-/

namespace PairwiseIndependence

/-- The branch-number formulation of MDS is symmetric under inversion. -/
theorem IsMDS.symm {A : Type*} [AddCommGroup A] [DecidableEq A] {n : ℕ}
    (L : State A n ≃+ State A n) (hMDS : IsMDS L) : IsMDS L.symm := by
  intro x hx
  have hy : L.symm x ≠ 0 := by
    intro hzero
    have h := congrArg L hzero
    exact hx (by simpa using h)
  have h := hMDS (L.symm x) hy
  simpa only [L.apply_symm_apply, add_comm] using h

section Keyed

variable {A : Type*} [AddCommGroup A] [Fintype A] {n : ℕ} {κ : Type*}

/-- Independent keys for each word of a parallel S-box layer. -/
def keyedSubstitute (S : κ → A ≃ A)
    (key : Fin n → κ) (x : State A n) : State A n :=
  fun i => S (key i) (x i)

/-- A two-round SHARK core with independent keys for every word in each
substitution layer, in addition to the uniform intermediate state key. -/
def keyedSharkTwoCore (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (key : (Fin n → κ) × (Fin n → κ) × State A n)
    (x : State A n) : State A n :=
  keyedSubstitute S key.2.1 (L (keyedSubstitute S key.1 x + key.2.2))

end Keyed

open scoped Matrix

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The unnormalised number of input pairs with difference `a` and output
difference `b`. -/
def differenceCount (f : A → A) (b a : A) : ℕ :=
  ∑ x : A, if f (x + a) = f x + b then 1 else 0

/-- Add a fresh, independent, uniform key between two deterministic functions. -/
def keyedComposition (f g : A → A) (key x : A) : A := g (f x + key)

/-- Compose two independently keyed families with a fresh uniform key at the
intermediate state. -/
def independentlyKeyedComposition {κ ι : Type*}
    (f : κ → A → A) (g : ι → A → A)
    (key : κ × ι × A) (x : A) : A :=
  g key.2.1 (f key.1 x + key.2.2)

private theorem sum_key_translation (g : A → A) (u d b : A) :
    (∑ key : A, if g (u + d + key) = g (u + key) + b then 1 else 0) =
      ∑ y : A, if g (y + d) = g y + b then 1 else 0 := by
  classical
  conv_lhs =>
    enter [2, key]
    rw [add_right_comm u d key]
  exact Fintype.sum_equiv (Equiv.addLeft u) _ _ (fun key => rfl)

private theorem sum_by_difference (f g : A → A) (b a : A) :
    (∑ x : A, differenceCount g b (f (x + a) - f x)) =
      ∑ d : A, differenceCount g b d * differenceCount f d a := by
  classical
  have hsingle (x : A) :
      differenceCount g b (f (x + a) - f x) =
        ∑ d : A, differenceCount g b d *
          (if f (x + a) = f x + d then 1 else 0) := by
    have hp (d : A) : (f (x + a) = f x + d) ↔ d = f (x + a) - f x := by
      constructor
      · intro h
        rw [h]
        simp
      · intro h
        rw [h]
        simp
    simp [hp]
  simp_rw [hsingle]
  rw [Finset.sum_comm]
  congr 1
  funext d
  simp only [differenceCount, Finset.mul_sum]

/-- The exact counting identity behind multiplication of difference-distribution
matrices. The key between `f` and `g` is averaged uniformly. -/
theorem differenceCount_keyedComposition (f g : A → A) (b a : A) :
    (∑ key : A, differenceCount (keyedComposition f g key) b a) =
      ∑ d : A, differenceCount g b d * differenceCount f d a := by
  classical
  calc
    _ = ∑ x : A, ∑ key : A,
          if g (f (x + a) + key) = g (f x + key) + b then 1 else 0 := by
      simp only [differenceCount, keyedComposition]
      rw [Finset.sum_comm]
    _ = ∑ x : A, differenceCount g b (f (x + a) - f x) := by
      apply Finset.sum_congr rfl
      intro x _
      have h : f (x + a) = f x + (f (x + a) - f x) := by abel
      conv_lhs =>
        enter [2, key]
        rw [h]
      exact sum_key_translation g (f x) (f (x + a) - f x) b
    _ = _ := sum_by_difference f g b a

private theorem differenceCount_independentlyKeyedComposition
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (f : κ → A → A) (g : ι → A → A) (b a : A) :
    (∑ key : κ × ι × A,
      differenceCount (independentlyKeyedComposition f g key) b a) =
      ∑ d : A,
        (∑ l : ι, differenceCount (g l) b d) *
          (∑ k : κ, differenceCount (f k) d a) := by
  classical
  simp only [Fintype.sum_prod_type]
  change (∑ k : κ, ∑ l : ι, ∑ t : A,
    differenceCount (keyedComposition (f k) (g l) t) b a) = _
  simp_rw [differenceCount_keyedComposition]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, l]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1
  funext d
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem deterministicDifferenceDistributionMatrix_eq_count
    (f : A → A) (b a : A) :
    deterministicDifferenceDistributionMatrix f b a =
      (differenceCount f b a : ℝ) / Fintype.card A := by
  have h : (differenceCount f b a : ℝ) =
      ∑ x : A, if f (x + a) = f x + b then (1 : ℝ) else 0 := by
    simp only [differenceCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h]
  simp only [deterministicDifferenceDistributionMatrix, differenceDistributionMatrix,
    Fintype.card_unit, one_mul, Fintype.sum_unique]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : f (x + a) = f x + b <;> simp [hp]

private theorem differenceDistributionMatrix_keyedComposition_eq_count
    (f g : A → A) (b a : A) :
    differenceDistributionMatrix (keyedComposition f g) b a =
      (∑ key : A, (differenceCount (keyedComposition f g key) b a : ℝ)) /
        ((Fintype.card A : ℝ) * Fintype.card A) := by
  have h : (∑ key : A, (differenceCount (keyedComposition f g key) b a : ℝ)) =
      ∑ key : A, ∑ x : A,
        if keyedComposition f g key (x + a) =
          keyedComposition f g key x + b then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro key _
    simp only [differenceCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h]
  simp only [differenceDistributionMatrix, Nat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro key _
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : keyedComposition f g key (x + a) =
      keyedComposition f g key x + b <;> simp [hp]

/-- A difference-distribution entry is the normalized finite difference count. -/
theorem differenceDistributionMatrix_eq_count
    {κ : Type*} [Fintype κ] (f : κ → A → A) (b a : A) :
    differenceDistributionMatrix f b a =
      (∑ key : κ, (differenceCount (f key) b a : ℝ)) /
        ((Fintype.card κ : ℝ) * Fintype.card A) := by
  have h : (∑ key : κ, (differenceCount (f key) b a : ℝ)) =
      ∑ key : κ, ∑ x : A,
        if f key (x + a) = f key x + b then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro key _
    simp only [differenceCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h]
  simp only [differenceDistributionMatrix, Nat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro key _
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : f key (x + a) = f key x + b <;> simp [hp]

/-- Inverting a bijection transposes its difference-distribution matrix. -/
theorem deterministicDifferenceDistributionMatrix_inverse_transpose
    (f : A ≃ A) :
    deterministicDifferenceDistributionMatrix (fun x => f.symm x) =
      (deterministicDifferenceDistributionMatrix (fun x => f x))ᵀ := by
  ext b a
  rw [Matrix.transpose_apply]
  simp only [deterministicDifferenceDistributionMatrix_eq_count]
  have hcount : differenceCount (fun x => f.symm x) b a =
      differenceCount (fun x => f x) a b := by
    unfold differenceCount
    calc
      (∑ y : A, if f.symm (y + a) = f.symm y + b then 1 else 0) =
          ∑ x : A, if f.symm (f x + a) = f.symm (f x) + b then 1 else 0 := by
        exact (Fintype.sum_equiv f _ _ (fun x => rfl)).symm
      _ = ∑ x : A, if f (x + b) = f x + a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        have hiff : f.symm (f x + a) = f.symm (f x) + b ↔
            f (x + b) = f x + a := by
          simp only [Equiv.symm_apply_apply]
          constructor
          · intro h
            calc
              f (x + b) = f (f.symm (f x + a)) := by rw [h]
              _ = f x + a := f.apply_symm_apply _
          · intro h
            rw [← h, f.symm_apply_apply]
        simp only [hiff]
  rw [hcount]

/-- A family of permutations never maps a nonzero input difference to zero. -/
theorem differenceDistributionMatrix_zero_output
    {κ : Type*} [Fintype κ] (f : κ → A → A)
    (hf : ∀ key, Function.Injective (f key)) {a : A} (ha : a ≠ 0) :
    differenceDistributionMatrix f 0 a = 0 := by
  rw [differenceDistributionMatrix_eq_count]
  have hcount (key : κ) : differenceCount (f key) 0 a = 0 := by
    unfold differenceCount
    apply Finset.sum_eq_zero
    intro x _
    have hne : f key (x + a) ≠ f key x := by
      intro h
      have hx : x + a = x := hf key h
      have : x + a = x + 0 := by simpa using hx
      exact ha (add_left_cancel this)
    simp [hne]
  simp [hcount]

/-- With a fresh uniform intermediate key, difference-distribution matrices
multiply in the same order as the functions compose. -/
theorem differenceDistributionMatrix_keyedComposition
    (f g : A → A) :
    differenceDistributionMatrix (keyedComposition f g) =
      deterministicDifferenceDistributionMatrix g *
        deterministicDifferenceDistributionMatrix f := by
  ext b a
  rw [Matrix.mul_apply, differenceDistributionMatrix_keyedComposition_eq_count]
  simp_rw [deterministicDifferenceDistributionMatrix_eq_count]
  have hcount :
      (∑ key : A, (differenceCount (keyedComposition f g key) b a : ℝ)) =
        ∑ d : A, (differenceCount g b d : ℝ) *
          (differenceCount f d a : ℝ) := by
    exact_mod_cast differenceCount_keyedComposition f g b a
  rw [hcount, Finset.sum_div]
  congr 1
  funext d
  ring

/-- Independent keyed families compose by multiplying their
difference-distribution matrices when a fresh uniform intermediate key is
included. This is the composition rule used throughout the paper. -/
theorem differenceDistributionMatrix_independentlyKeyedComposition
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (f : κ → A → A) (g : ι → A → A) :
    differenceDistributionMatrix (independentlyKeyedComposition f g) =
      differenceDistributionMatrix g * differenceDistributionMatrix f := by
  ext b a
  rw [Matrix.mul_apply,
    differenceDistributionMatrix_eq_count (independentlyKeyedComposition f g) b a]
  simp_rw [differenceDistributionMatrix_eq_count]
  have hcount :
      (∑ key : κ × ι × A,
        (differenceCount (independentlyKeyedComposition f g key) b a : ℝ)) =
      ∑ d : A,
        (∑ l : ι, (differenceCount (g l) b d : ℝ)) *
          (∑ k : κ, (differenceCount (f k) d a : ℝ)) := by
    exact_mod_cast differenceCount_independentlyKeyedComposition f g b a
  rw [hcount, Finset.sum_div]
  simp only [Fintype.card_prod, Nat.cast_mul]
  congr 1
  funext d
  ring

private theorem differenceCount_comp_addEquiv (g : A → A) (L : A ≃+ A)
    (b a : A) :
    differenceCount (g ∘ L) b a = differenceCount g b (L a) := by
  classical
  unfold differenceCount
  simp only [Function.comp_apply, map_add]
  exact Fintype.sum_equiv L.toEquiv _ _ (fun x => rfl)

/-- A deterministic additive permutation acts on the input-difference index. -/
theorem deterministicDifferenceDistributionMatrix_comp_addEquiv
    (g : A → A) (L : A ≃+ A) :
    deterministicDifferenceDistributionMatrix (g ∘ L) =
      deterministicDifferenceDistributionMatrix g *
        deterministicDifferenceDistributionMatrix (fun x => L x) := by
  ext b a
  rw [Matrix.mul_apply, deterministicDifferenceDistributionMatrix_eq_count,
    differenceCount_comp_addEquiv]
  have hL (d : A) :
      deterministicDifferenceDistributionMatrix (fun x : A => L x) d a =
        if L a = d then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom d a
  simp_rw [hL]
  simp only [mul_ite, mul_one, mul_zero]
  rw [show (∑ d : A, if L a = d then deterministicDifferenceDistributionMatrix g b d else 0) =
      deterministicDifferenceDistributionMatrix g b (L a) by simp]
  exact (deterministicDifferenceDistributionMatrix_eq_count g b (L a)).symm

/-- Theorem 3's two-round core has the paper's matrix factorization. -/
theorem sharkTwoCore_differenceDistributionMatrix
    {n : ℕ} (S : A ≃ A) (L : State A n ≃+ State A n) :
    differenceDistributionMatrix (sharkTwoCore S L) =
      (deterministicDifferenceDistributionMatrix (substitute S : State A n → State A n)) *
      (deterministicDifferenceDistributionMatrix (fun x : State A n => L x)) *
      (deterministicDifferenceDistributionMatrix (substitute S : State A n → State A n)) := by
  calc
    differenceDistributionMatrix (sharkTwoCore S L) =
        differenceDistributionMatrix
          (keyedComposition (substitute S) (substitute S ∘ L)) := rfl
    _ = deterministicDifferenceDistributionMatrix (substitute S ∘ L) *
          deterministicDifferenceDistributionMatrix (substitute S) :=
      differenceDistributionMatrix_keyedComposition _ _
    _ = _ := by
      rw [deterministicDifferenceDistributionMatrix_comp_addEquiv]

end PairwiseIndependence

import PairwiseIndependence.Pairwise.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.GroupTheory.Perm.Basic

/-!
# Difference-distribution matrices

The output difference indexes the row and the input difference indexes the column,
as in Equation (1) of `main.pdf`. A keyed function is averaged over a uniform key
and a uniform input. The definitions in this file do not presuppose AES or SHARK.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [Fintype κ]

/-- The difference-distribution matrix of a deterministic function: a keyed
family with a single key. -/
noncomputable def deterministicDifferenceDistributionMatrix (f : A → A) : Matrix A A ℝ :=
  differenceDistributionMatrix (fun _ : Unit => f)

/-- Uniform key averaging is invariant under a bijective key reindexing. -/
theorem differenceDistributionMatrix_key_reindex
    {A κ ι : Type*} [AddCommGroup A] [Fintype A]
    [Fintype κ] [Fintype ι]
    (e : κ ≃ ι) (f : ι → A → A) :
    differenceDistributionMatrix (fun key : κ => f (e key)) =
      differenceDistributionMatrix f := by
  classical
  ext b a
  unfold differenceDistributionMatrix
  rw [Fintype.card_congr e]
  exact congrArg (fun z : ℝ => z / ((Fintype.card ι * Fintype.card A : ℕ) : ℝ))
    (Fintype.sum_equiv e _ _ (fun key => rfl))

/-- The induced matrix one norm: the largest absolute column sum. This is the
norm used in Lemma 4 and Lemma 6 of the paper. -/
noncomputable def matrixOneNorm (D : Matrix A A ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩
    (fun a => ∑ b : A, |D b a|)

open Classical in
/-- The entries of `U`: a uniformly random permutation maps the zero difference
to zero and every nonzero difference to a uniformly random nonzero difference. -/
theorem uniformDifferenceDistributionMatrix_apply (b a : A) :
    uniformDifferenceDistributionMatrix A b a =
      if a = 0 then (if b = 0 then 1 else 0)
      else if b = 0 then 0 else 1 / ((Fintype.card A - 1 : ℕ) : ℝ) := by
  classical
  -- `c b` counts the pairs `(σ, x)` with `σ (x + a) = σ x + b`.
  let c : A → ℝ := fun b =>
    ∑ σ : Equiv.Perm A, ∑ x : A, if σ (x + a) = σ x + b then (1 : ℝ) else 0
  have hentry : uniformDifferenceDistributionMatrix A b a =
      c b / ((Fintype.card (Equiv.Perm A) * Fintype.card A : ℕ) : ℝ) := by
    simp only [uniformDifferenceDistributionMatrix, differenceDistributionMatrix, c]
  have hN : (0 : ℝ) < ((Fintype.card (Equiv.Perm A) * Fintype.card A : ℕ) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm A) * Fintype.card A :=
      Nat.mul_pos Fintype.card_pos Fintype.card_pos
    exact_mod_cast this
  -- Every pair `(σ, x)` has exactly one output difference.
  have h1 (σ : Equiv.Perm A) (x : A) :
      (∑ b : A, if σ (x + a) = σ x + b then (1 : ℝ) else 0) = 1 := by
    have hiff (b : A) : σ (x + a) = σ x + b ↔ b = σ (x + a) - σ x := by
      constructor
      · intro h; rw [h]; abel
      · intro h; rw [h]; abel
    simp only [hiff]
    simp
  have htotal : ∑ b, c b = ((Fintype.card (Equiv.Perm A) * Fintype.card A : ℕ) : ℝ) := by
    calc ∑ b, c b = ∑ σ : Equiv.Perm A, ∑ x : A, ∑ b : A,
          (if σ (x + a) = σ x + b then (1 : ℝ) else 0) := by
            simp only [c]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)
      _ = _ := by
            simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
              Nat.cast_mul]
  rw [hentry]
  by_cases ha : a = 0
  · subst ha
    have hc : c b =
        if b = 0 then ((Fintype.card (Equiv.Perm A) * Fintype.card A : ℕ) : ℝ) else 0 := by
      by_cases hb : b = 0
      · subst hb; simp [c]
      · simp [c, hb]
    rw [hc, if_pos rfl]
    by_cases hb : b = 0 <;> simp [hb]
  · -- No pair has output difference zero.
    have hzero : c 0 = 0 := by
      simp only [c]
      apply Finset.sum_eq_zero; intro σ _
      apply Finset.sum_eq_zero; intro x _
      simp [ha]
    -- All nonzero output differences are equally frequent.
    have hconst : ∀ b b' : A, b ≠ 0 → b' ≠ 0 → c b = c b' := by
      intro b b' hb hb'
      simp only [c]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      let Φ : Equiv.Perm A → Equiv.Perm A := fun σ => Equiv.swap (σ x + b) (σ x + b') * σ
      have hb0 (σ : Equiv.Perm A) : σ x ≠ σ x + b := by
        intro h; apply hb; simpa using h
      have hb0' (σ : Equiv.Perm A) : σ x ≠ σ x + b' := by
        intro h; apply hb'; simpa using h
      have hfix (σ : Equiv.Perm A) : Φ σ x = σ x := by
        simp only [Φ, Equiv.Perm.coe_mul, Function.comp_apply]
        exact Equiv.swap_apply_of_ne_of_ne (hb0 σ) (hb0' σ)
      have hinv : Function.Involutive Φ := by
        intro σ
        have h := hfix σ
        simp only [Φ] at h ⊢
        rw [h, ← mul_assoc, Equiv.swap_mul_self, one_mul]
      refine Fintype.sum_equiv hinv.toPerm _ _ (fun σ => ?_)
      have hiff : σ (x + a) = σ x + b ↔ Φ σ (x + a) = Φ σ x + b' := by
        rw [hfix]
        simp only [Φ, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_eq_iff,
          Equiv.swap_apply_right]
      simp only [Function.Involutive.coe_toPerm, hiff]
    by_cases hb : b = 0
    · subst hb; simp [hzero, ha]
    · -- `c` takes the value `c b` at each of the `N − 1` nonzero differences.
      have hsum : ∑ d, c d = (Fintype.card A - 1 : ℕ) * c b := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : A)), hzero, zero_add]
        rw [Finset.sum_congr rfl (fun d hd => hconst d b (Finset.ne_of_mem_erase hd) hb)]
        simp [Finset.card_erase_of_mem]
      rw [htotal] at hsum
      have hcb : c b ≠ 0 := by
        intro h
        rw [h, mul_zero] at hsum
        exact hN.ne' hsum
      simp only [ha, hb, if_false]
      rw [hsum, mul_comm, ← div_div, div_self hcb]

/-- The uniform difference-distribution matrix is symmetric. -/
theorem uniformDifferenceDistributionMatrix_transpose
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] :
    Matrix.transpose (uniformDifferenceDistributionMatrix A) =
      uniformDifferenceDistributionMatrix A := by
  ext a b
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [uniformDifferenceDistributionMatrix_apply, ha, hb]

theorem matrixOneNorm_le_iff (D : Matrix A A ℝ) (t : ℝ) :
    matrixOneNorm D ≤ t ↔ ∀ a : A, (∑ b : A, |D b a|) ≤ t := by
  classical
  simp only [matrixOneNorm, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem differenceDistributionMatrix_nonneg (f : κ → A → A) (b a : A) :
    0 ≤ differenceDistributionMatrix f b a := by
  classical
  unfold differenceDistributionMatrix
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> norm_num
  · exact Nat.cast_nonneg _

theorem differenceDistributionMatrix_zero_input [Nonempty κ] [DecidableEq A]
    (f : κ → A → A) (b : A) :
    differenceDistributionMatrix f b 0 = if b = 0 then 1 else 0 := by
  classical
  by_cases hb : b = 0
  · subst b
    simp [differenceDistributionMatrix]
  · simp [differenceDistributionMatrix, hb]

/-- An additive map has a deterministic differential transition. -/
theorem deterministicDifferenceDistributionMatrix_addHom [DecidableEq A]
    (L : A →+ A) (b a : A) :
    deterministicDifferenceDistributionMatrix (fun x => L x) b a =
      if L a = b then 1 else 0 := by
  classical
  by_cases h : L a = b
  · simp [deterministicDifferenceDistributionMatrix, differenceDistributionMatrix, map_add, h]
  · simp [deterministicDifferenceDistributionMatrix, differenceDistributionMatrix, map_add, h]

end PairwiseIndependence

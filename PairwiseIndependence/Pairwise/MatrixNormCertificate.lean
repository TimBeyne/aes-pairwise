import PairwiseIndependence.Pairwise.SingularValuesTail
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Quadratic-form certificates for the Euclidean matrix norm

A rational positive-semidefinite certificate can bound the norm of a
real symmetric matrix without evaluating any square roots in its entries.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symmetric matrix `M` has Euclidean operator norm at most `c` if
both `c I + M` and `c I - M` are positive semidefinite. -/
theorem matrix_twoNorm_le_of_posSemidef_bounds
    (M : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hplus : Matrix.PosSemidef (c • (1 : Matrix ι ι ℝ) + M))
    (hminus : Matrix.PosSemidef (c • (1 : Matrix ι ι ℝ) - M)) :
    ‖M‖ ≤ c := by
  have hM : M.IsHermitian := by
    have hp := hplus.1.eq
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial] at hp
    exact add_left_cancel hp
  let b := hM.eigenvectorBasis
  let e := hM.eigenvalues
  have hdiag (i : ι) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) M (b i) = e i • b i := by
    apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.linearEquiv_apply,
      WithLp.toLp_smul] using hM.mulVec_eigenvectorBasis i
  have he (i : ι) : |e i| ≤ c := by
    have hp := hplus.2 ⇑(b i)
    have hm := hminus.2 ⇑(b i)
    rw [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hM.mulVec_eigenvectorBasis i] at hp
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hM.mulVec_eigenvectorBasis i] at hm
    have hunit : star ⇑(b i) ⬝ᵥ ⇑(b i) = (1 : ℝ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      norm_num
    change 0 ≤ star ⇑(b i) ⬝ᵥ (c • ⇑(b i) + e i • ⇑(b i)) at hp
    change 0 ≤ star ⇑(b i) ⬝ᵥ (c • ⇑(b i) - e i • ⇑(b i)) at hm
    simp only [smul_eq_mul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, hunit, mul_one] at hp hm
    rw [abs_le]
    constructor <;> linarith
  rw [Matrix.cstar_norm_def]
  exact norm_le_of_orthonormalBasis_diagonal b
    (Matrix.toEuclideanCLM (𝕜 := ℝ) M) e c hc hdiag he

/-- A quadratic-form certificate may be checked before an orthonormalizing
change of coordinates. This is the form used for the rational activity matrix. -/
theorem matrix_twoNorm_le_of_gram_posSemidef_bounds
    (G M R : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (horth : Rᵀ * G * R = 1)
    (hplus : Matrix.PosSemidef (c • G + M))
    (hminus : Matrix.PosSemidef (c • G - M)) :
    ‖Rᵀ * M * R‖ ≤ c := by
  have hp : Matrix.PosSemidef (Rᵀ * (c • G + M) * R) := by
    simpa only [Matrix.conjTranspose, star_trivial] using
      hplus.conjTranspose_mul_mul_same R
  have hm : Matrix.PosSemidef (Rᵀ * (c • G - M) * R) := by
    simpa only [Matrix.conjTranspose, star_trivial] using
      hminus.conjTranspose_mul_mul_same R
  have hplus' : Matrix.PosSemidef
      (c • (1 : Matrix ι ι ℝ) + Rᵀ * M * R) := by
    convert hp using 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, horth]
  have hminus' : Matrix.PosSemidef
      (c • (1 : Matrix ι ι ℝ) - Rᵀ * M * R) := by
    convert hm using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, horth]
  exact matrix_twoNorm_le_of_posSemidef_bounds _ c hc hplus' hminus'

/-- A real symmetric matrix whose nonnegative diagonal dominates the sum of
absolute off-diagonal entries in every row is positive semidefinite. This
form makes a finite residual certificate checkable by rational arithmetic. -/
theorem matrix_posSemidef_of_diagonalDominant
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i) :
    M.PosSemidef := by
  apply hM.posSemidef_of_eigenvalues_nonneg
  intro i
  let v : ι → ℝ := ⇑(hM.eigenvectorBasis i)
  have hvne : v ≠ 0 := hM.eigenvectorBasis.orthonormal.ne_zero i
  have hv : M *ᵥ v = hM.eigenvalues i • v :=
    hM.mulVec_eigenvectorBasis i
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M) (hM.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact ⟨Module.End.mem_eigenspace_iff.mpr (by simpa only [Matrix.toLin'_apply] using hv),
      hvne⟩
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball heig
  rw [mem_closedBall_iff_norm', Real.norm_eq_abs] at hk
  have hk' := (abs_le.mp hk).2
  have hrowk := hrow k
  simp only [Real.norm_eq_abs] at hk'
  linarith

/-- A positive-semidefinite Gram residual certifies a Euclidean operator
norm bound. The one-word S-box certificate can therefore work with the
symmetric rational matrix `c²I − MᵀM`. -/
theorem matrix_twoNorm_le_of_gram_residual_posSemidef
    (M : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hresidual : Matrix.PosSemidef
      (c ^ 2 • (1 : Matrix ι ι ℝ) - Mᴴ * M)) :
    ‖M‖ ≤ c := by
  let G := Mᴴ * M
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hcI : (c ^ 2 • (1 : Matrix ι ι ℝ)).PosSemidef := by
    have hdiag : (Matrix.diagonal (fun _ : ι => c ^ 2)).PosSemidef :=
      Matrix.PosSemidef.diagonal (by
        intro i
        change (0 : ℝ) ≤ c ^ 2
        positivity)
    convert hdiag using 1
    ext i j
    simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  have hplus : Matrix.PosSemidef
      (c ^ 2 • (1 : Matrix ι ι ℝ) + G) := hcI.add hG
  have hminus : Matrix.PosSemidef
      (c ^ 2 • (1 : Matrix ι ι ℝ) - G) := hresidual
  have hnorm := matrix_twoNorm_le_of_posSemidef_bounds G (c ^ 2)
    (sq_nonneg c) hplus hminus
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hnorm
  nlinarith [norm_nonneg M]

end PairwiseIndependence

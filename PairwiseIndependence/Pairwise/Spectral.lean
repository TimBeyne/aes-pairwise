import PairwiseIndependence.Pairwise.Activity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The paper's spectral-weight subspaces

This file begins the decomposition `V⊥ = W₁ ⊕ ⋯ ⊕ Wₙ` used for the
spectral terms in Theorem 3. A one-word factor belongs either to the
two-dimensional activity space or to its orthogonal complement. A tensor
with exactly `l` complementary factors generates `W_l`.

The paper later chooses an orthonormal basis for the complementary factors
to estimate matrix coordinates. The generators below allow every vector in
that complement, and the paper's basis columns are proved to span the same
space.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}

/-- The one-word indicator `δ₀`. -/
noncomputable def wordZeroIndicator (a : A) : ℝ :=
  if a = 0 then 1 else 0

/-- The one-word indicator `δ_{𝔽_q}`. -/
def wordAllIndicator (_a : A) : ℝ := 1

/-- The paper's one-word space `A = Span {δ₀, δ_{𝔽_q}}`. -/
noncomputable def wordActivitySubspace : Submodule ℝ (A → ℝ) :=
  Submodule.span ℝ ({wordZeroIndicator (A := A), wordAllIndicator (A := A)} :
    Set (A → ℝ))

/-- The one-word activity space inside the Euclidean function space. -/
noncomputable def wordActivityHilbertSubspace :
    Submodule ℝ (EuclideanSpace ℝ A) :=
  (wordActivitySubspace (A := A)).map
    (WithLp.linearEquiv 2 ℝ (A → ℝ)).symm.toLinearMap

/-- The orthonormal basis for the one-word activity complement used by
the paper in its spectral Frobenius calculation. We choose mathlib's
standard finite-dimensional orthonormal basis; the calculation must be
independent of the choice. -/
noncomputable def wordComplementOrthonormalBasis :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
      ℝ (wordActivityHilbertSubspace (A := A))ᗮ :=
  stdOrthonormalBasis ℝ (wordActivityHilbertSubspace (A := A))ᗮ

/-- A basis vector of the paper's one-word activity complement, in
function coordinates. -/
noncomputable def wordComplementBasisVector
    (j : Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    A → ℝ :=
  (WithLp.linearEquiv 2 ℝ (A → ℝ))
    ((wordComplementOrthonormalBasis (A := A) j :
      (wordActivityHilbertSubspace (A := A))ᗮ) : EuclideanSpace ℝ A)

/-- The completeness kernel of the paper's one-word complementary
orthonormal basis. -/
noncomputable def wordComplementBasisKernel (a b : A) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
    wordComplementBasisVector (A := A) j a *
      wordComplementBasisVector (A := A) j b

theorem mem_wordActivityHilbertSubspace_iff
    (v : EuclideanSpace ℝ A) :
    v ∈ wordActivityHilbertSubspace (A := A) ↔
      (WithLp.linearEquiv 2 ℝ (A → ℝ)) v ∈
        wordActivitySubspace (A := A) := by
  unfold wordActivityHilbertSubspace
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨(WithLp.linearEquiv 2 ℝ (A → ℝ)) v, hv, by simp⟩

/-- Orthogonality to the one-word activity space, in the paper's dot product. -/
def InWordActivityOrthogonalComplement (f : A → ℝ) : Prop :=
  ∀ g ∈ wordActivitySubspace (A := A), g ⬝ᵥ f = 0

/-- The dot-product and Hilbert-space descriptions of the one-word
orthogonal complement agree. -/
theorem inWordActivityOrthogonalComplement_iff_mem_orthogonal
    (v : EuclideanSpace ℝ A) :
    InWordActivityOrthogonalComplement
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) ↔
      v ∈ (wordActivityHilbertSubspace (A := A))ᗮ := by
  have hinner (x y : EuclideanSpace ℝ A) :
      ⟪x, y⟫ =
        ((WithLp.linearEquiv 2 ℝ (A → ℝ)) x) ⬝ᵥ
          ((WithLp.linearEquiv 2 ℝ (A → ℝ)) y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [WithLp.linearEquiv_apply, dotProduct_comm]
  constructor
  · intro hv
    apply ((wordActivityHilbertSubspace (A := A)).mem_orthogonal' v).2
    intro g hg
    rw [hinner, dotProduct_comm]
    exact hv _ ((mem_wordActivityHilbertSubspace_iff g).mp hg)
  · intro hv g hg
    have hg' : WithLp.toLp 2 g ∈ wordActivityHilbertSubspace (A := A) :=
      (mem_wordActivityHilbertSubspace_iff (WithLp.toLp 2 g)).2 (by simpa using hg)
    have hpair :=
      ((wordActivityHilbertSubspace (A := A)).mem_orthogonal' v).1 hv
        (WithLp.toLp 2 g) hg'
    rw [hinner] at hpair
    change ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) ⬝ᵥ g = 0 at hpair
    rwa [dotProduct_comm] at hpair

theorem wordComplementBasisVector_orthogonal
    (j : Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    InWordActivityOrthogonalComplement (wordComplementBasisVector (A := A) j) := by
  exact (inWordActivityOrthogonalComplement_iff_mem_orthogonal _).mpr
    (wordComplementOrthonormalBasis (A := A) j).property

/-- Every vector orthogonal to the two one-word activity directions
expands in the paper's chosen orthonormal complement basis. -/
theorem wordComplementBasisVector_sum_repr
    (v : A → ℝ) (hv : InWordActivityOrthogonalComplement v) :
    ∃ c : Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) → ℝ,
      v = ∑ j, c j • wordComplementBasisVector (A := A) j := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  let qv : Q := ⟨WithLp.toLp 2 v,
    (inWordActivityOrthogonalComplement_iff_mem_orthogonal
      (WithLp.toLp 2 v)).mp (by simpa using hv)⟩
  let b := wordComplementOrthonormalBasis (A := A)
  let c : Fin (Module.finrank ℝ Q) → ℝ := fun j => b.toBasis.repr qv j
  refine ⟨c, ?_⟩
  have hsum := b.toBasis.sum_repr qv
  have hsumE : ((∑ j, c j • b j : Q) : EuclideanSpace ℝ A) =
      (qv : EuclideanSpace ℝ A) := by
    exact congrArg Subtype.val hsum
  have hcoord := congrArg (WithLp.linearEquiv 2 ℝ (A → ℝ)) hsumE
  simpa [qv, b, c, wordComplementBasisVector,
    map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] using hcoord.symm

theorem wordComplementBasisVector_mem_span
    (v : A → ℝ) (hv : InWordActivityOrthogonalComplement v) :
    v ∈ Submodule.span ℝ
      (Set.range (wordComplementBasisVector (A := A))) := by
  obtain ⟨c, hsum⟩ := wordComplementBasisVector_sum_repr v hv
  rw [hsum]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j))

/-- The paper's one-word complementary basis is orthonormal in the
coordinate dot product. -/
theorem wordComplementBasisVector_dotProduct
    (i j : Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    wordComplementBasisVector (A := A) i ⬝ᵥ
      wordComplementBasisVector (A := A) j =
      if i = j then 1 else 0 := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  let b := wordComplementOrthonormalBasis (A := A)
  have h := (orthonormal_iff_ite.mp b.orthonormal) i j
  rw [Q.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [b, Q, wordComplementBasisVector,
    WithLp.linearEquiv_apply, dotProduct_comm] using h

/-- The basis-completeness kernel is the coordinate matrix of
orthogonal projection onto the one-word activity complement. -/
theorem wordComplementBasisKernel_eq_projection (a b : A) :
    wordComplementBasisKernel (A := A) a b =
      (WithLp.linearEquiv 2 ℝ (A → ℝ))
        (((wordActivityHilbertSubspace (A := A))ᗮ.orthogonalProjection
          (WithLp.toLp 2 (Pi.single b (1 : ℝ))) :
          (wordActivityHilbertSubspace (A := A))ᗮ) :
          EuclideanSpace ℝ A) a := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  let e : EuclideanSpace ℝ A := WithLp.toLp 2 (Pi.single b (1 : ℝ))
  let p : Q := Q.orthogonalProjection e
  let B := wordComplementOrthonormalBasis (A := A)
  have hcoeff (j : Fin (Module.finrank ℝ Q)) :
      B.toBasis.repr p j = wordComplementBasisVector (A := A) j b := by
    change B.repr p j = _
    rw [OrthonormalBasis.repr_apply_apply]
    rw [Q.inner_orthogonalProjection_eq_of_mem_left]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [e, B, wordComplementBasisVector,
      WithLp.linearEquiv_apply, dotProduct]
  have hsum := B.toBasis.sum_repr p
  have hsumE : ((∑ j, B.toBasis.repr p j • B j : Q) :
      EuclideanSpace ℝ A) = (p : EuclideanSpace ℝ A) :=
    congrArg Subtype.val hsum
  have hcoord := congrArg (WithLp.linearEquiv 2 ℝ (A → ℝ)) hsumE
  have ha := congrFun hcoord a
  simp_rw [hcoeff] at ha
  simpa [wordComplementBasisKernel, p, e, B, Q,
    map_sum, map_smul, wordComplementBasisVector,
    Submodule.coe_sum, Submodule.coe_smul, mul_comm] using ha

/-- Every one-word vector splits into an activity part and an orthogonal
part, using mathlib's orthogonal projection. -/
theorem wordVector_activity_add_orthogonal (f : A → ℝ) :
    ∃ g h : A → ℝ,
      g ∈ wordActivitySubspace (A := A) ∧
      InWordActivityOrthogonalComplement h ∧ f = g + h := by
  let K := wordActivityHilbertSubspace (A := A)
  let v : EuclideanSpace ℝ A := WithLp.toLp 2 f
  let p := K.orthogonalProjection v
  let g : A → ℝ := (WithLp.linearEquiv 2 ℝ (A → ℝ))
    (p : EuclideanSpace ℝ A)
  let h : A → ℝ := (WithLp.linearEquiv 2 ℝ (A → ℝ))
    (v - (p : EuclideanSpace ℝ A))
  have hg : g ∈ wordActivitySubspace (A := A) :=
    (mem_wordActivityHilbertSubspace_iff
      (p : EuclideanSpace ℝ A)).mp p.property
  have hr : v - (p : EuclideanSpace ℝ A) ∈ Kᗮ :=
    K.sub_starProjection_mem_orthogonal v
  have hh : InWordActivityOrthogonalComplement h :=
    (inWordActivityOrthogonalComplement_iff_mem_orthogonal
      (v - (p : EuclideanSpace ℝ A))).2 hr
  refine ⟨g, h, hg, hh, ?_⟩
  have hsum : g + h = f := by
    dsimp [g, h]
    funext a
    simp [Pi.add_apply, Pi.sub_apply, v]
  exact hsum.symm

/-- The one-word factor selected by an activity bit. -/
noncomputable def activityWordVector (b : Bool) : A → ℝ :=
  if b then wordAllIndicator (A := A) else wordZeroIndicator (A := A)

omit [Fintype A] in
theorem activityWordVector_mem_wordActivitySubspace (b : Bool) :
    activityWordVector (A := A) b ∈ wordActivitySubspace (A := A) := by
  cases b
  · exact Submodule.subset_span (by simp [activityWordVector])
  · exact Submodule.subset_span (by simp [activityWordVector])

omit [Fintype A] in
/-- The paper's two one-word activity indicators are linearly independent
as soon as the alphabet has a nonzero element. -/
theorem activityWordVector_linearIndependent
    (u : A) (hu : u ≠ 0) :
    LinearIndependent ℝ (activityWordVector (A := A)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have h0 := congrFun hc (0 : A)
  have hu' := congrFun hc u
  simp [Finset.sum_apply, Pi.smul_apply, activityWordVector,
    wordZeroIndicator, wordAllIndicator, hu] at h0 hu'
  cases b <;> linarith

omit [Fintype A] in
/-- The paper's one-word activity space has dimension two. -/
theorem wordActivitySubspace_finrank (u : A) (hu : u ≠ 0) :
    Module.finrank ℝ (wordActivitySubspace (A := A)) = 2 := by
  have hspan : wordActivitySubspace (A := A) =
      Submodule.span ℝ (Set.range (activityWordVector (A := A))) := by
    simp [wordActivitySubspace, Bool.range_eq, activityWordVector]
  rw [hspan, finrank_span_eq_card (activityWordVector_linearIndependent u hu)]
  simp

theorem wordActivityHilbertSubspace_finrank (u : A) (hu : u ≠ 0) :
    Module.finrank ℝ (wordActivityHilbertSubspace (A := A)) = 2 := by
  unfold wordActivityHilbertSubspace
  rw [LinearEquiv.finrank_map_eq]
  exact wordActivitySubspace_finrank u hu

/-- The one-word complementary basis has exactly `q - 2` vectors, as
assumed in the paper's Frobenius-coordinate count. -/
theorem wordActivityOrthogonal_finrank (u : A) (hu : u ≠ 0) :
    Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ =
      Fintype.card A - 2 := by
  have h := (wordActivityHilbertSubspace (A := A)).finrank_add_finrank_orthogonal
  rw [wordActivityHilbertSubspace_finrank u hu,
    finrank_euclideanSpace] at h
  omega

/-- For the paper's alphabet sizes, the one-word complementary basis has a reference vector, so every complementary-position set admits a reference spectral column. -/
theorem wordActivityOrthogonal_finrank_pos_of_card_ge_three
    (hq : 3 ≤ Fintype.card A) :
    0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ := by
  letI : Nontrivial A := (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  rw [wordActivityOrthogonal_finrank u hu]
  omega

/-- The normalized one-word activity factor used in the paper's `W_l`
matrix `B_l`: `δ₀` or `δ_all / √q`. -/
noncomputable def normalizedActivityWordVector (b : Bool) : A → ℝ :=
  if b then (Real.sqrt (Fintype.card A : ℝ))⁻¹ • wordAllIndicator (A := A)
  else wordZeroIndicator (A := A)

omit [DecidableEq A] in
/-- Squaring the normalization from `m` all-indicator word factors gives
the paper's denominator `q^m`. -/
theorem normalizedAllIndicatorFactor_sq (m : ℕ) :
    (((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ m) ^ 2 =
      ((Fintype.card A : ℝ)⁻¹) ^ m := by
  have hq : (0 : ℝ) ≤ Fintype.card A := by positivity
  calc
    (((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ m) ^ 2 =
        (((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ 2) ^ m := by
      rw [← pow_mul, ← pow_mul]
      ring
    _ = ((Fintype.card A : ℝ)⁻¹) ^ m := by
      rw [inv_pow, Real.sq_sqrt hq]

theorem normalizedActivityWordVector_mem_wordActivitySubspace (b : Bool) :
    normalizedActivityWordVector (A := A) b ∈ wordActivitySubspace (A := A) := by
  cases b
  · exact Submodule.subset_span (by simp [normalizedActivityWordVector])
  · exact (wordActivitySubspace (A := A)).smul_mem _
      (Submodule.subset_span (by simp))

/-- The two normalized activity factors have Gram matrix with diagonal
entries one and off-diagonal entries `1/√q`. -/
theorem normalizedActivityWordVector_dotProduct (b c : Bool) :
    normalizedActivityWordVector (A := A) b ⬝ᵥ
      normalizedActivityWordVector (A := A) c =
      if b = c then 1 else (Real.sqrt (Fintype.card A : ℝ))⁻¹ := by
  have hq : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < Fintype.card A)
  have hsqrt : Real.sqrt (Fintype.card A : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hsq := Real.sq_sqrt (le_of_lt hq)
  cases b <;> cases c <;>
    simp [normalizedActivityWordVector, wordZeroIndicator,
      wordAllIndicator, dotProduct]
  · field_simp [hsqrt]

/-- The two normalized activity factors still span the paper's
two-dimensional one-word activity space. -/
theorem wordActivitySubspace_le_span_normalizedActivityWordVector :
    wordActivitySubspace (A := A) ≤
      Submodule.span ℝ
        (Set.range (normalizedActivityWordVector (A := A))) := by
  let P := Submodule.span ℝ
    (Set.range (normalizedActivityWordVector (A := A)))
  have hq : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < Fintype.card A)
  have hsqrt : Real.sqrt (Fintype.card A : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have htrue : wordAllIndicator (A := A) =
      Real.sqrt (Fintype.card A : ℝ) •
        normalizedActivityWordVector (A := A) true := by
    funext a
    simp [normalizedActivityWordVector, wordAllIndicator,
      smul_eq_mul, hsqrt]
  unfold wordActivitySubspace
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with hzero | hall
  · rw [hzero]
    exact Submodule.subset_span
      (Set.mem_range.mpr ⟨false, by simp [normalizedActivityWordVector]⟩)
  · rw [hall, htrue]
    exact P.smul_mem _
      (Submodule.subset_span (Set.mem_range_self true))

/-- The pure tensor of one-word vectors, written in state coordinates. -/
def spectralTensor (f : Fin n → A → ℝ) : State A n → ℝ :=
  fun x => ∏ i : Fin n, f i (x i)

/-- The paper's `W_l`: the span of pure tensors with exactly `l` factors in
the one-word orthogonal complement. -/
noncomputable def spectralWeightSubspace (l : ℕ) :
    Submodule ℝ (State A n → ℝ) :=
  Submodule.span ℝ {v | ∃ (I : Finset (Fin n)) (f : Fin n → A → ℝ),
    I.card = l ∧
      (∀ i ∈ I, InWordActivityOrthogonalComplement (f i)) ∧
      (∀ i ∉ I, f i ∈ wordActivitySubspace (A := A)) ∧
      v = spectralTensor f}

/-- The actual column index for the paper's `B_l`: choose the `l`
complementary positions, an orthonormal complement vector at each such
position, and one of the two normalized activity vectors elsewhere. -/
abbrev SpectralBasisIndex (l : ℕ) : Type _ :=
  Σ I : {I : Finset (Fin n) // I.card = l},
    ({i : Fin n // i ∈ I.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
    ({i : Fin n // i ∉ I.1} → Bool)

/-- The paper's spectral basis matrix `B_l`, with no redundant choices
outside the word positions where they are used. -/
noncomputable def spectralBasisMatrix (l : ℕ) :
    Matrix (State A n) (SpectralBasisIndex (A := A) (n := n) l) ℝ :=
  fun a c => spectralTensor (fun i =>
    if hi : i ∈ c.1.1 then
      wordComplementBasisVector (A := A) (c.2.1 ⟨i, hi⟩)
    else normalizedActivityWordVector (A := A) (c.2.2 ⟨i, hi⟩)) a

/-- The one-word factor of a column of the paper's `B_l` matrix. -/
noncomputable def spectralBasisWordFactor (l : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l)
    (i : Fin n) : A → ℝ :=
  if hi : i ∈ c.1.1 then
    wordComplementBasisVector (A := A) (c.2.1 ⟨i, hi⟩)
  else normalizedActivityWordVector (A := A) (c.2.2 ⟨i, hi⟩)

/-- The `2n` one-word factors in a pairing of columns of
`B_{l₁}` and `B_{l₂}` across an MDS linear layer. Input coordinates
come from the right column and output coordinates from the left. -/
noncomputable def spectralBasisGraphFactor
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Sum (Fin n) (Fin n) → A → ℝ :=
  Sum.elim (spectralBasisWordFactor l₂ d)
    (spectralBasisWordFactor l₁ c)

/-- Positions with a complementary one-word basis factor in a pairing
of columns of `B_{l₁}` and `B_{l₂}`. -/
noncomputable def spectralBasisGraphComplementPositions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Finset (Sum (Fin n) (Fin n)) := by
  classical
  exact Finset.univ.filter (fun j =>
    match j with
    | Sum.inl i => i ∈ d.1.1
    | Sum.inr i => i ∈ c.1.1)

/-- Positions with the zero-indicator activity factor in a pairing of
columns of `B_{l₁}` and `B_{l₂}`. -/
noncomputable def spectralBasisGraphZeroPositions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Finset (Sum (Fin n) (Fin n)) := by
  classical
  exact Finset.univ.filter (fun j =>
    match j with
    | Sum.inl i =>
        if hi : i ∈ d.1.1 then False else d.2.2 ⟨i, hi⟩ = false
    | Sum.inr i =>
        if hi : i ∈ c.1.1 then False else c.2.2 ⟨i, hi⟩ = false)

theorem spectralBasisGraphZeroPositions_disjoint_complementPositions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Disjoint (spectralBasisGraphZeroPositions l₁ l₂ c d)
      (spectralBasisGraphComplementPositions l₁ l₂ c d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjz hjc
  cases j with
  | inl i =>
      have hi : i ∈ d.1.1 := by
        simpa [spectralBasisGraphComplementPositions] using hjc
      simp [spectralBasisGraphZeroPositions, hi] at hjz
  | inr i =>
      have hi : i ∈ c.1.1 := by
        simpa [spectralBasisGraphComplementPositions] using hjc
      simp [spectralBasisGraphZeroPositions, hi] at hjz

/-- A pairing of a `B_{l₁}` column with a `B_{l₂}` column has exactly
`l₁ + l₂` complementary graph-position factors, the paper's parameter
`l` in its Frobenius calculation. -/
theorem spectralBasisGraphComplementPositions_card
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (spectralBasisGraphComplementPositions l₁ l₂ c d).card = l₁ + l₂ := by
  classical
  have hfilter :
      spectralBasisGraphComplementPositions l₁ l₂ c d =
        d.1.1.image Sum.inl ∪ c.1.1.image Sum.inr := by
    ext j
    cases j <;> simp [spectralBasisGraphComplementPositions]
  rw [hfilter]
  have hdisj : Disjoint (d.1.1.image Sum.inl) (c.1.1.image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro j hj₁ hj₂
    rcases Finset.mem_image.mp hj₁ with ⟨i, _, rfl⟩
    simp at hj₂
  rw [Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective,
    d.1.2, c.1.2]
  omega

/-- Choosing a zero-indicator or normalized all-indicator at each of a
finite collection of graph positions is equivalent to choosing the set
of zero-indicator positions. -/
noncomputable def activityBitsZeroSetEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun f := Finset.univ.filter (fun i => f i = false)
  invFun s i := if i ∈ s then false else true
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv s := by
    ext i
    simp

/-- The number of activity-bit choices with `k` zero-indicator factors
on `m` available graph positions is `m.choose k`. -/
theorem activityBitsZeroSet_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Fintype.card {f : ι → Bool // (activityBitsZeroSetEquiv f).card = k} =
      Nat.choose (Fintype.card ι) k := by
  classical
  let e : {f : ι → Bool // (activityBitsZeroSetEquiv f).card = k} ≃
      {s : Finset ι // s.card = k} :=
    activityBitsZeroSetEquiv.subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun s : Finset ι => s.card = k)) =
      (Finset.univ : Finset ι).powersetCard k := by
    ext s
    simp
  rw [hset, Finset.card_powersetCard]
  simp

/-- The graph positions outside the complementary set are the disjoint union of the input and output activity positions. -/
noncomputable def spectralBasisGraphActivityPositionEquiv
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    ({i : Fin n // i ∉ d.1.1} ⊕ {i : Fin n // i ∉ c.1.1}) ≃
      {j : Sum (Fin n) (Fin n) //
        j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} := by
  classical
  refine {
    toFun := fun x => match x with
      | Sum.inl i => ⟨Sum.inl i.1, by
          simpa [spectralBasisGraphComplementPositions] using i.2⟩
      | Sum.inr i => ⟨Sum.inr i.1, by
          simpa [spectralBasisGraphComplementPositions] using i.2⟩
    invFun := by
      intro j
      rcases j with ⟨j, hj⟩
      cases j with
      | inl i =>
          exact Sum.inl ⟨i, by
            simpa [spectralBasisGraphComplementPositions] using hj⟩
      | inr i =>
          exact Sum.inr ⟨i, by
            simpa [spectralBasisGraphComplementPositions] using hj⟩
    left_inv := by intro x; cases x <;> rfl
    right_inv := by intro j; rcases j with ⟨j, hj⟩; cases j <;> rfl
  }

/-- The activity-bit choices in the two spectral columns are equivalent to one Boolean choice at every noncomplementary graph position. -/
noncomputable def spectralBasisGraphActivityChoicesEquiv
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (({i : Fin n // i ∉ d.1.1} → Bool) ×
     ({i : Fin n // i ∉ c.1.1} → Bool)) ≃
      ({j : Sum (Fin n) (Fin n) //
        j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} → Bool) :=
  (Equiv.sumPiEquivProdPi (fun _ :
    ({i : Fin n // i ∉ d.1.1} ⊕ {i : Fin n // i ∉ c.1.1}) => Bool)).symm.trans
    ((spectralBasisGraphActivityPositionEquiv l₁ l₂ c d).piCongrLeft
      (fun _ => Bool))

theorem spectralBasisGraphActivityPositions_card
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Fintype.card {j : Sum (Fin n) (Fin n) //
      j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} =
        2 * n - (l₁ + l₂) := by
  classical
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  have htotal : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp
    omega
  have hcardI : I.card = l₁ + l₂ :=
    spectralBasisGraphComplementPositions_card l₁ l₂ c d
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun j : Sum (Fin n) (Fin n) => j ∉ I)) = Iᶜ := by
    ext j
    simp
  rw [hfilter, Finset.card_compl]
  rw [htotal, hcardI]

/-- With complementary positions fixed, the number of activity-bit choices having exactly `k` zero-indicator positions is `choose (2n-l₁-l₂) k`. -/
theorem spectralBasisGraphActivityChoices_card
    (l₁ l₂ k : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Fintype.card {p :
      (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)) //
      (activityBitsZeroSetEquiv (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d p)).card = k} =
        Nat.choose (2 * n - (l₁ + l₂)) k := by
  classical
  let e := spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d
  let e' : {p : (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)) //
      (activityBitsZeroSetEquiv (e p)).card = k} ≃
      {f : ({j : Sum (Fin n) (Fin n) //
        j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} → Bool) //
        (activityBitsZeroSetEquiv f).card = k} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr e']
  rw [activityBitsZeroSet_card]
  rw [spectralBasisGraphActivityPositions_card]

theorem spectralBasisGraphActivityChoicesEquiv_inl
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (g : {i : Fin n // i ∉ d.1.1} → Bool)
    (f : {i : Fin n // i ∉ c.1.1} → Bool)
    (i : {i : Fin n // i ∉ d.1.1}) :
    spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (g, f)
      ((spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) (Sum.inl i)) = g i := by
  exact Equiv.piCongrLeft_sumInl
    (π := fun _ : {j : Sum (Fin n) (Fin n) //
      j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} => Bool)
    (spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) g f i

theorem spectralBasisGraphActivityChoicesEquiv_inr
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (g : {i : Fin n // i ∉ d.1.1} → Bool)
    (f : {i : Fin n // i ∉ c.1.1} → Bool)
    (i : {i : Fin n // i ∉ c.1.1}) :
    spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (g, f)
      ((spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) (Sum.inr i)) = f i := by
  exact Equiv.piCongrLeft_sumInr
    (π := fun _ : {j : Sum (Fin n) (Fin n) //
      j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} => Bool)
    (spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) g f i

theorem mem_spectralBasisGraphZeroPositions_iff_activityBit_false
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (j : {j : Sum (Fin n) (Fin n) //
      j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d}) :
    j.1 ∈ spectralBasisGraphZeroPositions l₁ l₂ c d ↔
      spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (d.2.2, c.2.2) j = false := by
  classical
  obtain ⟨x, rfl⟩ :=
    (spectralBasisGraphActivityPositionEquiv l₁ l₂ c d).surjective j
  cases x with
  | inl x =>
      rw [spectralBasisGraphActivityChoicesEquiv_inl]
      simp [spectralBasisGraphActivityPositionEquiv,
        spectralBasisGraphZeroPositions, x.2]
  | inr x =>
      rw [spectralBasisGraphActivityChoicesEquiv_inr]
      simp [spectralBasisGraphActivityPositionEquiv,
        spectralBasisGraphZeroPositions, x.2]

/-- The canonical zero-indicator graph-position set has the same cardinality as the zero set of the combined activity-bit function. -/
theorem spectralBasisGraphZeroPositions_card_eq_activityBitsZeroSet_card
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (spectralBasisGraphZeroPositions l₁ l₂ c d).card =
      (activityBitsZeroSetEquiv
        (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (d.2.2, c.2.2))).card := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  let B : Finset {j : Sum (Fin n) (Fin n) // j ∉ I} :=
    activityBitsZeroSetEquiv
      (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (d.2.2, c.2.2))
  have hdisj : Disjoint Z I :=
    spectralBasisGraphZeroPositions_disjoint_complementPositions l₁ l₂ c d
  have himage : B.image Subtype.val = Z := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
      have hbit :
          spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (d.2.2, c.2.2) r = false := by
        simpa [B, activityBitsZeroSetEquiv] using hr
      exact (mem_spectralBasisGraphZeroPositions_iff_activityBit_false l₁ l₂ c d r).2 hbit
    · intro hj
      have hnot : j ∉ I := by
        intro hI
        exact Finset.disjoint_left.mp hdisj hj hI
      let r : {j : Sum (Fin n) (Fin n) // j ∉ I} := ⟨j, hnot⟩
      apply Finset.mem_image.mpr
      refine ⟨r, ?_, rfl⟩
      have hbit := (mem_spectralBasisGraphZeroPositions_iff_activityBit_false l₁ l₂ c d r).1 hj
      simpa [B, activityBitsZeroSetEquiv] using hbit
  change Z.card = B.card
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]

/-- Replace only the activity bits of a spectral basis column, keeping its complementary positions and one-word basis choices fixed. -/
noncomputable def spectralBasisIndex_withActivityChoices
    (l : ℕ) (c : SpectralBasisIndex (A := A) (n := n) l)
    (z : {i : Fin n // i ∉ c.1.1} → Bool) :
    SpectralBasisIndex (A := A) (n := n) l :=
  ⟨c.1, (c.2.1, z)⟩

/-- Changing activity bits leaves the equivalence from pairs of activity choices to graph-position choices unchanged. -/
theorem spectralBasisGraphActivityChoicesEquiv_withActivityChoices
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (f : {i : Fin n // i ∉ c.1.1} → Bool)
    (g : {i : Fin n // i ∉ d.1.1} → Bool) :
    spectralBasisGraphActivityChoicesEquiv l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c f)
      (spectralBasisIndex_withActivityChoices l₂ d g) =
        spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d := by
  apply Equiv.ext
  intro p
  rcases p with ⟨pg, pf⟩
  funext j
  obtain ⟨x, rfl⟩ :=
    (spectralBasisGraphActivityPositionEquiv l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c f)
      (spectralBasisIndex_withActivityChoices l₂ d g)).surjective j
  cases x with
  | inl x =>
      rw [spectralBasisGraphActivityChoicesEquiv_inl]
      change pg x = spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (pg, pf)
        ((spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) (Sum.inl x))
      rw [spectralBasisGraphActivityChoicesEquiv_inl]
  | inr x =>
      rw [spectralBasisGraphActivityChoicesEquiv_inr]
      change pf x = spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (pg, pf)
        ((spectralBasisGraphActivityPositionEquiv l₁ l₂ c d) (Sum.inr x))
      rw [spectralBasisGraphActivityChoicesEquiv_inr]

/-- For fixed complementary positions, the graph zero count depends only on the chosen activity bits. -/
theorem spectralBasisGraphZeroPositions_card_withActivityChoices
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (f : {i : Fin n // i ∉ c.1.1} → Bool)
    (g : {i : Fin n // i ∉ d.1.1} → Bool) :
    (spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c f)
      (spectralBasisIndex_withActivityChoices l₂ d g)).card =
      (activityBitsZeroSetEquiv
        (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d (g, f))).card := by
  have h := spectralBasisGraphZeroPositions_card_eq_activityBitsZeroSet_card
    l₁ l₂ (spectralBasisIndex_withActivityChoices l₁ c f)
      (spectralBasisIndex_withActivityChoices l₂ d g)
  simpa only [spectralBasisGraphActivityChoicesEquiv_withActivityChoices] using h

/-- With complementary positions and basis vectors fixed, exactly `choose (2n-l₁-l₂) k` activity choices give `k` zero positions in the paper's graph. -/
theorem spectralBasisGraphActivityChoices_card_actualZeroPositions
    (l₁ l₂ k : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    Fintype.card {p :
      (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)) //
      (spectralBasisGraphZeroPositions l₁ l₂
        (spectralBasisIndex_withActivityChoices l₁ c p.2)
        (spectralBasisIndex_withActivityChoices l₂ d p.1)).card = k} =
        Nat.choose (2 * n - (l₁ + l₂)) k := by
  classical
  let e : {p : (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)) //
      (spectralBasisGraphZeroPositions l₁ l₂
        (spectralBasisIndex_withActivityChoices l₁ c p.2)
        (spectralBasisIndex_withActivityChoices l₂ d p.1)).card = k} ≃
      {p : (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)) //
      (activityBitsZeroSetEquiv
        (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d p)).card = k} :=
    (Equiv.refl _).subtypeEquiv (fun p => by
      rw [spectralBasisGraphZeroPositions_card_withActivityChoices]
      rfl)
  rw [Fintype.card_congr e]
  exact spectralBasisGraphActivityChoices_card l₁ l₂ k c d

/-- For fixed complementary positions, summing any weight of the actual number `k` of zero-indicator graph factors over activity choices is the paper's binomial sum. -/
theorem spectralBasisGraphActivityChoices_sum_by_zeroCount
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (F : ℕ → ℝ) :
    (∑ p : (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)),
      F ((spectralBasisGraphZeroPositions l₁ l₂
        (spectralBasisIndex_withActivityChoices l₁ c p.2)
        (spectralBasisIndex_withActivityChoices l₂ d p.1)).card)) =
      ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
        (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) * F k := by
  classical
  let P := (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool))
  let K := 2 * n - (l₁ + l₂)
  let count : P → ℕ := fun p =>
    (spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c p.2)
      (spectralBasisIndex_withActivityChoices l₂ d p.1)).card
  have hcount (p : P) : count p ≤ K := by
    change (spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c p.2)
      (spectralBasisIndex_withActivityChoices l₂ d p.1)).card ≤ _
    rw [spectralBasisGraphZeroPositions_card_withActivityChoices]
    calc
      (activityBitsZeroSetEquiv
        (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d p)).card ≤
          Fintype.card {j : Sum (Fin n) (Fin n) //
            j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d} := by
              simpa using Finset.card_le_card (Finset.subset_univ
                (activityBitsZeroSetEquiv
                  (spectralBasisGraphActivityChoicesEquiv l₁ l₂ c d p)))
      _ = K := spectralBasisGraphActivityPositions_card l₁ l₂ c d
  have hmap (p : P) (_hp : p ∈ (Finset.univ : Finset P)) :
      count p ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by
        have := hcount p
        omega)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset P)) (t := Finset.range (K + 1))
    (g := count) hmap (fun p => F (count p))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ p ∈ (Finset.univ : Finset P) with count p = k, F (count p)) =
        ∑ p ∈ (Finset.univ : Finset P) with count p = k, F k := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
    _ = ((Finset.univ.filter (fun p : P => count p = k)).card : ℝ) * F k := by
      simp
    _ = (Nat.choose K k : ℝ) * F k := by
      congr 1
      rw [← Fintype.card_subtype]
      exact_mod_cast spectralBasisGraphActivityChoices_card_actualZeroPositions
        l₁ l₂ k c d

/-- The complementary graph positions are the disjoint union of the input and output complementary positions. -/
noncomputable def spectralBasisGraphComplementPositionEquiv
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    ({i : Fin n // i ∈ d.1.1} ⊕ {i : Fin n // i ∈ c.1.1}) ≃
      {j : Sum (Fin n) (Fin n) //
        j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d} := by
  classical
  refine {
    toFun := fun x => match x with
      | Sum.inl i => ⟨Sum.inl i.1, by
          simp [spectralBasisGraphComplementPositions, i.2]⟩
      | Sum.inr i => ⟨Sum.inr i.1, by
          simp [spectralBasisGraphComplementPositions, i.2]⟩
    invFun := by
      intro j
      rcases j with ⟨j, hj⟩
      cases j with
      | inl i =>
          exact Sum.inl ⟨i, by
            simpa [spectralBasisGraphComplementPositions] using hj⟩
      | inr i =>
          exact Sum.inr ⟨i, by
            simpa [spectralBasisGraphComplementPositions] using hj⟩
    left_inv := by intro x; cases x <;> rfl
    right_inv := by intro j; rcases j with ⟨j, hj⟩; cases j <;> rfl
  }

/-- A pair of one-word basis choices for the two spectral columns is equivalent to one choice at every complementary graph position. -/
noncomputable def spectralBasisGraphComplementChoicesEquiv
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (({i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
     ({i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))) ≃
      ({j : Sum (Fin n) (Fin n) //
        j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :=
  (Equiv.sumPiEquivProdPi (fun _ :
    ({i : Fin n // i ∈ d.1.1} ⊕ {i : Fin n // i ∈ c.1.1}) =>
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))).symm.trans
    ((spectralBasisGraphComplementPositionEquiv l₁ l₂ c d).piCongrLeft
      (fun _ => Fin (Module.finrank ℝ
        (wordActivityHilbertSubspace (A := A))ᗮ)))

theorem spectralBasisGraphComplementChoicesEquiv_inl
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (g : {i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (i : {i : Fin n // i ∈ d.1.1}) :
    spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d (g, f)
      ((spectralBasisGraphComplementPositionEquiv l₁ l₂ c d) (Sum.inl i)) = g i := by
  exact Equiv.piCongrLeft_sumInl
    (π := fun _ : {j : Sum (Fin n) (Fin n) //
      j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d} =>
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (spectralBasisGraphComplementPositionEquiv l₁ l₂ c d) g f i

theorem spectralBasisGraphComplementChoicesEquiv_inr
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (g : {i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (i : {i : Fin n // i ∈ c.1.1}) :
    spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d (g, f)
      ((spectralBasisGraphComplementPositionEquiv l₁ l₂ c d) (Sum.inr i)) = f i := by
  exact Equiv.piCongrLeft_sumInr
    (π := fun _ : {j : Sum (Fin n) (Fin n) //
      j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d} =>
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (spectralBasisGraphComplementPositionEquiv l₁ l₂ c d) g f i

/-- Summing over the complementary-basis choices in the two columns counts each combined graph-position choice exactly once. -/
theorem spectralBasisGraphComplementChoices_sum
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (F : ({j : Sum (Fin n) (Fin n) //
      j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) → ℝ) :
    (∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        F (spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d (g, f))) =
      ∑ j, F j := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d)
    (fun p => F (spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d p)) F (by intro p; rfl)

/-- Replace only the complementary one-word basis choices of a paper-style spectral column. -/
noncomputable def spectralBasisIndex_withComplementChoices
    (l : ℕ) (c : SpectralBasisIndex (A := A) (n := n) l)
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    SpectralBasisIndex (A := A) (n := n) l :=
  ⟨c.1, (f, c.2.2)⟩

theorem spectralBasisGraphComplementPositions_withChoices
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (g : {i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    spectralBasisGraphComplementPositions l₁ l₂
      (spectralBasisIndex_withComplementChoices l₁ c f)
      (spectralBasisIndex_withComplementChoices l₂ d g) =
        spectralBasisGraphComplementPositions l₁ l₂ c d := by
  rfl

theorem spectralBasisGraphZeroPositions_withChoices
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (g : {i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
    spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withComplementChoices l₁ c f)
      (spectralBasisIndex_withComplementChoices l₂ d g) =
        spectralBasisGraphZeroPositions l₁ l₂ c d := by
  rfl

/-- On a complementary graph position, replacing the two columns' basis choices agrees with the combined graph-position choice. -/
theorem spectralBasisGraphFactor_withChoices_of_mem_complement
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (f : {i : Fin n // i ∈ c.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (g : {i : Fin n // i ∈ d.1.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (i : {j : Sum (Fin n) (Fin n) //
      j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d}) :
    spectralBasisGraphFactor l₁ l₂
      (spectralBasisIndex_withComplementChoices l₁ c f)
      (spectralBasisIndex_withComplementChoices l₂ d g) i.1 =
        wordComplementBasisVector (A := A)
          (spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d (g, f) i) := by
  classical
  obtain ⟨x, rfl⟩ :=
    (spectralBasisGraphComplementPositionEquiv l₁ l₂ c d).surjective i
  cases x with
  | inl x =>
      rw [spectralBasisGraphComplementChoicesEquiv_inl]
      simp [spectralBasisGraphComplementPositionEquiv,
        spectralBasisGraphFactor, spectralBasisWordFactor,
        spectralBasisIndex_withComplementChoices, x.2]
  | inr x =>
      rw [spectralBasisGraphComplementChoicesEquiv_inr]
      simp [spectralBasisGraphComplementPositionEquiv,
        spectralBasisGraphFactor, spectralBasisWordFactor,
        spectralBasisIndex_withComplementChoices, x.2]

/-- The remaining normalized all-indicator positions number
`2n - k - (l₁ + l₂)`, where `k` is the number of zero-indicator positions.
This is the paper's normalization exponent in the Frobenius sum. -/
theorem spectralBasisGraphUniformPositions_card
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
    let I := spectralBasisGraphComplementPositions l₁ l₂ c d
    ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card =
      2 * n - Z.card - (l₁ + l₂) := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  have hdisj : Disjoint Z I :=
    spectralBasisGraphZeroPositions_disjoint_complementPositions l₁ l₂ c d
  have hcardI : I.card = l₁ + l₂ :=
    spectralBasisGraphComplementPositions_card l₁ l₂ c d
  have htotal : (Finset.univ : Finset (Sum (Fin n) (Fin n))).card = 2 * n := by
    simp
    omega
  have hcardUnion : (Z ∪ I).card = Z.card + I.card :=
    Finset.card_union_of_disjoint hdisj
  have hsub : Z ∪ I ⊆ (Finset.univ : Finset (Sum (Fin n) (Fin n))) :=
    Finset.subset_univ _
  have hcardDiff := Finset.card_sdiff hsub
  change ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card =
    2 * n - Z.card - (l₁ + l₂)
  rw [hcardDiff, htotal, hcardUnion, hcardI]
  omega

/-- Every position in the canonical complementary set carries one of
the paper's orthonormal complementary one-word basis vectors. -/
theorem spectralBasisGraphFactor_eq_complement_of_mem_complementPositions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (j : Sum (Fin n) (Fin n))
    (hj : j ∈ spectralBasisGraphComplementPositions l₁ l₂ c d) :
    ∃ k : Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ),
      spectralBasisGraphFactor l₁ l₂ c d j =
        wordComplementBasisVector (A := A) k := by
  classical
  cases j with
  | inl i =>
      have hi : i ∈ d.1.1 := by
        simpa [spectralBasisGraphComplementPositions] using hj
      refine ⟨d.2.1 ⟨i, hi⟩, ?_⟩
      simp [spectralBasisGraphFactor, spectralBasisWordFactor, hi]
  | inr i =>
      have hi : i ∈ c.1.1 := by
        simpa [spectralBasisGraphComplementPositions] using hj
      refine ⟨c.2.1 ⟨i, hi⟩, ?_⟩
      simp [spectralBasisGraphFactor, spectralBasisWordFactor, hi]

theorem spectralBasisGraphFactor_eq_zero_of_mem_zeroPositions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (j : Sum (Fin n) (Fin n))
    (hj : j ∈ spectralBasisGraphZeroPositions l₁ l₂ c d) :
    spectralBasisGraphFactor l₁ l₂ c d j =
      wordZeroIndicator (A := A) := by
  classical
  cases j with
  | inl i =>
      by_cases hi : i ∈ d.1.1
      · simp [spectralBasisGraphZeroPositions, hi] at hj
      · have hb : d.2.2 ⟨i, hi⟩ = false := by
          simpa [spectralBasisGraphZeroPositions, hi] using hj
        simp [spectralBasisGraphFactor, spectralBasisWordFactor,
          normalizedActivityWordVector, hi, hb]
  | inr i =>
      by_cases hi : i ∈ c.1.1
      · simp [spectralBasisGraphZeroPositions, hi] at hj
      · have hb : c.2.2 ⟨i, hi⟩ = false := by
          simpa [spectralBasisGraphZeroPositions, hi] using hj
        simp [spectralBasisGraphFactor, spectralBasisWordFactor,
          normalizedActivityWordVector, hi, hb]

theorem spectralBasisGraphFactor_eq_uniform_of_not_mem_positions
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (j : Sum (Fin n) (Fin n))
    (hj : j ∉ spectralBasisGraphZeroPositions l₁ l₂ c d ∪
      spectralBasisGraphComplementPositions l₁ l₂ c d) :
    spectralBasisGraphFactor l₁ l₂ c d j =
      fun _ => (Real.sqrt (Fintype.card A : ℝ))⁻¹ := by
  classical
  have hz : j ∉ spectralBasisGraphZeroPositions l₁ l₂ c d := by
    intro h
    exact hj (Finset.mem_union.mpr (Or.inl h))
  have hc : j ∉ spectralBasisGraphComplementPositions l₁ l₂ c d := by
    intro h
    exact hj (Finset.mem_union.mpr (Or.inr h))
  cases j with
  | inl i =>
      have hi : i ∉ d.1.1 := by
        intro h
        apply hc
        simp [spectralBasisGraphComplementPositions, h]
      have hb : d.2.2 ⟨i, hi⟩ = true := by
        cases hbit : d.2.2 ⟨i, hi⟩ with
        | false =>
            exfalso
            apply hz
            simp [spectralBasisGraphZeroPositions, hi, hbit]
        | true => rfl
      funext a
      simp [spectralBasisGraphFactor, spectralBasisWordFactor,
        normalizedActivityWordVector, wordAllIndicator, hi, hb,
        smul_eq_mul]
  | inr i =>
      have hi : i ∉ c.1.1 := by
        intro h
        apply hc
        simp [spectralBasisGraphComplementPositions, h]
      have hb : c.2.2 ⟨i, hi⟩ = true := by
        cases hbit : c.2.2 ⟨i, hi⟩ with
        | false =>
            exfalso
            apply hz
            simp [spectralBasisGraphZeroPositions, hi, hbit]
        | true => rfl
      funext a
      simp [spectralBasisGraphFactor, spectralBasisWordFactor,
        normalizedActivityWordVector, wordAllIndicator, hi, hb,
        smul_eq_mul]

/-- The span of the columns of the paper's spectral basis matrix. -/
noncomputable def spectralBasisColumnSubspace (l : ℕ) :
    Submodule ℝ (State A n → ℝ) :=
  Submodule.span ℝ
    (Set.range (fun c : SpectralBasisIndex (A := A) (n := n) l =>
      fun a => spectralBasisMatrix (A := A) (n := n) l a c))

/-- Every column of the paper's `B_l` lies in `W_l`. -/
theorem spectralBasisMatrix_column_mem (l : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l) :
    (fun a => spectralBasisMatrix (A := A) (n := n) l a c) ∈
      spectralWeightSubspace (A := A) (n := n) l := by
  apply Submodule.subset_span
  refine ⟨c.1.1, (fun i => if hi : i ∈ c.1.1 then
    wordComplementBasisVector (A := A) (c.2.1 ⟨i, hi⟩)
    else normalizedActivityWordVector (A := A) (c.2.2 ⟨i, hi⟩)),
    c.1.2, ?_, ?_, rfl⟩
  · intro i hi
    simpa [hi] using wordComplementBasisVector_orthogonal
      (A := A) (c.2.1 ⟨i, hi⟩)
  · intro i hi
    simpa [hi] using normalizedActivityWordVector_mem_wordActivitySubspace
      (A := A) (c.2.2 ⟨i, hi⟩)

/-- The sum of all spectral-weight spaces from `W₀` through `Wₙ`. -/
noncomputable def spectralTotalSubspace :
    Submodule ℝ (State A n → ℝ) :=
  ⨆ l : Fin (n + 1), spectralWeightSubspace (A := A) (n := n) l

/-- The algebraic dot-product subspace corresponding to the paper's `V⊥`. -/
def activityAlgebraicOrthogonalSubspace :
    Submodule ℝ (State A n → ℝ) where
  carrier := {w | InActivityOrthogonalComplement w}
  zero_mem' := by
    intro v _
    simp
  add_mem' := by
    intro x y hx hy v hv
    rw [dotProduct_add, hx v hv, hy v hv, add_zero]
  smul_mem' := by
    intro t x hx v hv
    simp [dotProduct_smul, hx v hv]

/-- The sum `W₁ ⊕ ⋯ ⊕ Wₙ`, indexed by `Fin n`. -/
noncomputable def positiveSpectralSubspace :
    Submodule ℝ (State A n → ℝ) :=
  ⨆ l : Fin n, spectralWeightSubspace (A := A) (n := n) (l.val + 1)

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- Multilinearity of a pure tensor in a single word coordinate. -/
theorem spectralTensor_update_add
    (f : Fin n → A → ℝ) (i : Fin n) (g h : A → ℝ)
    (hi : f i = g + h) :
    spectralTensor f =
      spectralTensor (Function.update f i g) +
        spectralTensor (Function.update f i h) := by
  classical
  funext x
  have hsplit (t : Fin n → A → ℝ) :
      spectralTensor t x = t i (x i) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, t j (x j) := by
    exact (Finset.mul_prod_erase Finset.univ
      (fun j : Fin n => t j (x j)) (Finset.mem_univ i)).symm
  have herase (v : A → ℝ) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (Function.update f i v) j (x j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hji]
  rw [Pi.add_apply, hsplit f, hsplit (Function.update f i g),
    hsplit (Function.update f i h), herase g, herase h]
  simp only [Function.update_self]
  have hfi := congrFun hi (x i)
  simp only [Pi.add_apply] at hfi
  rw [hfi]
  ring

/-- Every pure tensor belongs to the sum of the paper's `W_l` spaces. -/
theorem spectralTensor_mem_spectralTotalSubspace
    (f : Fin n → A → ℝ) :
    spectralTensor f ∈ spectralTotalSubspace (A := A) (n := n) := by
  classical
  have hprocess (s : Finset (Fin n)) :
      ∀ f : Fin n → A → ℝ,
        (∀ i, i ∉ s →
          f i ∈ wordActivitySubspace (A := A) ∨
            InWordActivityOrthogonalComplement (f i)) →
        spectralTensor f ∈ spectralTotalSubspace (A := A) (n := n) := by
    induction s using Finset.induction_on with
    | empty =>
        intro f hf
        let I : Finset (Fin n) := Finset.univ.filter
          (fun i => f i ∉ wordActivitySubspace (A := A))
        have horth (i : Fin n) (hi : i ∈ I) :
            InWordActivityOrthogonalComplement (f i) := by
          have hnot : f i ∉ wordActivitySubspace (A := A) :=
            (Finset.mem_filter.mp hi).2
          exact (hf i (by simp)).resolve_left hnot
        have hact (i : Fin n) (hi : i ∉ I) :
            f i ∈ wordActivitySubspace (A := A) := by
          by_contra hnot
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnot⟩)
        have hW : spectralTensor f ∈
            spectralWeightSubspace (A := A) (n := n) I.card := by
          apply Submodule.subset_span
          exact ⟨I, f, rfl, horth, hact, rfl⟩
        have hcard : I.card < n + 1 := by
          have hle : I.card ≤ n := by
            calc
              I.card ≤ (Finset.univ : Finset (Fin n)).card :=
                Finset.card_le_card (Finset.subset_univ I)
              _ = n := by simp
          omega
        exact Submodule.mem_iSup_of_mem (⟨I.card, hcard⟩ : Fin (n + 1)) hW
    | @insert i s his ih =>
        intro f hf
        obtain ⟨g, h, hg, hh, hfi⟩ := wordVector_activity_add_orthogonal (f i)
        let fg := Function.update f i g
        let fh := Function.update f i h
        have hfg (j : Fin n) (hj : j ∉ s) :
            fg j ∈ wordActivitySubspace (A := A) ∨
              InWordActivityOrthogonalComplement (fg j) := by
          by_cases hji : j = i
          · subst j
            simp [fg, hg]
          · have hjold : j ∉ insert i s := by simp [hji, hj]
            simpa [fg, hji] using hf j hjold
        have hfh (j : Fin n) (hj : j ∉ s) :
            fh j ∈ wordActivitySubspace (A := A) ∨
              InWordActivityOrthogonalComplement (fh j) := by
          by_cases hji : j = i
          · subst j
            simp [fh, hh]
          · have hjold : j ∉ insert i s := by simp [hji, hj]
            simpa [fh, hji] using hf j hjold
        rw [spectralTensor_update_add f i g h hfi]
        exact (spectralTotalSubspace (A := A) (n := n)).add_mem
          (ih fg hfg) (ih fh hfh)
  exact hprocess Finset.univ f (by simp)

omit [AddCommGroup A] [Fintype A] in
/-- A point indicator of the state space is a pure tensor of one-word point
indicators. -/
theorem statePointIndicator_eq_spectralTensor (a : State A n) :
    (Pi.single a (1 : ℝ) : State A n → ℝ) =
      spectralTensor (fun i b => if b = a i then 1 else 0) := by
  classical
  funext x
  by_cases hxa : x = a
  · subst x
    simp [spectralTensor]
  · have hbad : ∃ i : Fin n, x i ≠ a i := by
      by_contra h
      push_neg at h
      exact hxa (funext h)
    obtain ⟨i, hi⟩ := hbad
    have hprod :
        (∏ j : Fin n, if x j = a j then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hxa, spectralTensor, hprod]

/-- All point indicators belong to the sum of the `W_l` spaces. -/
theorem statePointIndicator_mem_spectralTotalSubspace
    (a : State A n) :
    (Pi.single a (1 : ℝ) : State A n → ℝ) ∈
      spectralTotalSubspace (A := A) (n := n) := by
  rw [statePointIndicator_eq_spectralTensor]
  exact spectralTensor_mem_spectralTotalSubspace _

/-- The spectral-weight spaces span the full difference-vector space. -/
theorem spectralTotalSubspace_eq_top :
    spectralTotalSubspace (A := A) (n := n) = ⊤ := by
  classical
  apply top_unique
  intro v _
  have hsum :
      (∑ a : State A n, Pi.single a (v a)) = v := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hsum]
  apply Submodule.sum_mem
  intro a _
  have heq : (Pi.single a (v a) : State A n → ℝ) =
      v a • (Pi.single a (1 : ℝ) : State A n → ℝ) := by
    funext x
    by_cases hxa : x = a <;> simp [Pi.single_apply, hxa]
  rw [heq]
  exact (spectralTotalSubspace (A := A) (n := n)).smul_mem _
    (statePointIndicator_mem_spectralTotalSubspace a)

omit [AddCommGroup A] [DecidableEq A] in
/-- A state tensor dot product factors into one-word dot products. -/
theorem spectralTensor_dot (f g : Fin n → A → ℝ) :
    spectralTensor f ⬝ᵥ spectralTensor g =
      ∏ i : Fin n, (f i ⬝ᵥ g i) := by
  classical
  change (∑ x : Fin n → A,
    (∏ i : Fin n, f i (x i)) * (∏ i : Fin n, g i (x i))) =
      ∏ i : Fin n, ∑ a : A, f i a * g i a
  simp only [← Finset.prod_mul_distrib]
  simpa using (Finset.sum_prod_piFinset (s := Finset.univ)
    (g := fun i a => f i a * g i a))

omit [Fintype A] in
/-- The activity-box indicator is a pure tensor of the two one-word
activity indicators. -/
theorem activityBoxIndicator_eq_spectralTensor (z : Fin n → Bool) :
    activityBoxIndicator (A := A) z =
      spectralTensor (fun i => activityWordVector (A := A) (z i)) := by
  classical
  funext x
  by_cases hx : InActivityBox z x
  · have hterm (i : Fin n) :
        activityWordVector (A := A) (z i) (x i) = 1 := by
      cases hzi : z i <;>
        simp [activityWordVector, wordZeroIndicator, wordAllIndicator]
      exact hx i hzi
    simp [activityBoxIndicator, hx, spectralTensor, hterm]
  · have hbad : ∃ i : Fin n, z i = false ∧ x i ≠ 0 := by
      unfold InActivityBox at hx
      push_neg at hx
      exact hx
    obtain ⟨i, hzi, hxi⟩ := hbad
    have hterm : activityWordVector (A := A) (z i) (x i) = 0 := by
      simp [activityWordVector, wordZeroIndicator, hzi, hxi]
    have hprod :
        (∏ j : Fin n, activityWordVector (A := A) (z j) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hterm
    simp [activityBoxIndicator, hx, spectralTensor, hprod]

/-- Every activity-box indicator belongs to `W₀`. -/
theorem activityBoxIndicator_mem_spectralWeightZero (z : Fin n → Bool) :
    activityBoxIndicator (A := A) z ∈
      spectralWeightSubspace (A := A) (n := n) 0 := by
  rw [activityBoxIndicator_eq_spectralTensor]
  apply Submodule.subset_span
  refine ⟨∅, (fun i => activityWordVector (A := A) (z i)), by simp, ?_, ?_, rfl⟩
  · intro i hi
    simp at hi
  · intro i _
    exact activityWordVector_mem_wordActivitySubspace (z i)

/-- The paper's activity subspace `V` is contained in `W₀`. -/
theorem activitySubspace_le_spectralWeightZero :
    activitySubspace (A := A) (n := n) ≤
      spectralWeightSubspace (A := A) (n := n) 0 := by
  unfold activitySubspace
  apply Submodule.span_le.mpr
  rintro v ⟨z, rfl⟩
  exact activityBoxIndicator_mem_spectralWeightZero z

/-- A one-word factor lifted to state coordinate `i`. -/
def liftWordVector (i : Fin n) (f : A → ℝ) : State A n → ℝ :=
  fun x => f (x i)

omit [Fintype A] in
/-- An arbitrary word-activity vector, lifted to one state coordinate,
belongs to the paper's activity subspace `V`. -/
theorem liftWordVector_mem_activitySubspace
    (i : Fin n) (f : A → ℝ)
    (hf : f ∈ wordActivitySubspace (A := A)) :
    liftWordVector i f ∈ activitySubspace (A := A) (n := n) := by
  have hzero : liftWordVector i (wordZeroIndicator (A := A)) =
      activityBoxIndicator (A := A)
        (fun j : Fin n => if j = i then false else true) := by
    funext x
    have hiff : InActivityBox
        (fun j : Fin n => if j = i then false else true) x ↔ x i = 0 := by
      constructor
      · intro h
        exact h i (by simp)
      · intro hi j hj
        by_cases hji : j = i
        · simpa [hji] using hi
        · simp [hji] at hj
    change (if x i = 0 then (1 : ℝ) else 0) =
      if InActivityBox (fun j : Fin n => if j = i then false else true) x
      then 1 else 0
    by_cases hi : x i = 0
    · have hb := hiff.mpr hi
      simp only [if_pos hi, if_pos hb]
    · have hno : ¬ InActivityBox
          (fun j : Fin n => if j = i then false else true) x :=
        fun h => hi (hiff.mp h)
      simp only [if_neg hi, if_neg hno]
  have hall : liftWordVector i (wordAllIndicator (A := A)) =
      activityBoxIndicator (A := A) (fun _ : Fin n => true) := by
    funext x
    simp [liftWordVector, wordAllIndicator, activityBoxIndicator, InActivityBox]
  change f ∈ Submodule.span ℝ
    ({wordZeroIndicator (A := A), wordAllIndicator (A := A)} : Set (A → ℝ)) at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [hzero]
        exact activityBoxIndicator_mem_activitySubspace _
      · rw [hall]
        exact activityBoxIndicator_mem_activitySubspace _
  | zero =>
      have heq : liftWordVector i (0 : A → ℝ) = 0 := by
        funext x
        rfl
      rw [heq]
      exact (activitySubspace (A := A) (n := n)).zero_mem
  | add f g _ _ hF hG =>
      have heq : liftWordVector i (f + g) =
          liftWordVector i f + liftWordVector i g := by
        funext x
        simp [liftWordVector]
      rw [heq]
      exact (activitySubspace (A := A) (n := n)).add_mem hF hG
  | smul t f _ hF =>
      have heq : liftWordVector i (t • f) = t • liftWordVector i f := by
        funext x
        simp [liftWordVector]
      rw [heq]
      exact (activitySubspace (A := A) (n := n)).smul_mem t hF

omit [Fintype A] in
/-- A pure tensor whose every one-word factor is in the activity space
belongs to `V`. -/
theorem spectralTensor_mem_activitySubspace
    (f : Fin n → A → ℝ)
    (hf : ∀ i, f i ∈ wordActivitySubspace (A := A)) :
    spectralTensor f ∈ activitySubspace (A := A) (n := n) := by
  classical
  have hpartial (s : Finset (Fin n)) :
      (fun x : State A n => ∏ i ∈ s, f i (x i)) ∈
        activitySubspace (A := A) (n := n) := by
    induction s using Finset.induction_on with
    | empty =>
        have hones : (fun _ : State A n => (1 : ℝ)) =
            activityBoxIndicator (A := A) (fun _ : Fin n => true) := by
          funext x
          simp [activityBoxIndicator, InActivityBox]
        simpa [hones] using
          (activityBoxIndicator_mem_activitySubspace (A := A)
            (n := n) (fun _ : Fin n => true))
    | @insert i s hi ih =>
        have hmul := activitySubspace_mul_mem
          (liftWordVector i (f i))
          (fun x : State A n => ∏ j ∈ s, f j (x j))
          (liftWordVector_mem_activitySubspace i (f i) (hf i)) ih
        have heq :
            (fun x : State A n => ∏ j ∈ insert i s, f j (x j)) =
              liftWordVector i (f i) *
                (fun x : State A n => ∏ j ∈ s, f j (x j)) := by
          funext x
          simp [Finset.prod_insert hi, liftWordVector]
        rw [heq]
        exact hmul
  simpa [spectralTensor] using hpartial Finset.univ

/-- The paper's `W₀` is exactly its activity subspace `V`. -/
theorem spectralWeightZero_eq_activitySubspace :
    spectralWeightSubspace (A := A) (n := n) 0 =
      activitySubspace (A := A) (n := n) := by
  apply le_antisymm
  · unfold spectralWeightSubspace
    apply Submodule.span_le.mpr
    rintro v ⟨I, f, hcard, _, hrest, rfl⟩
    have hIempty : I = ∅ := Finset.card_eq_zero.mp hcard
    apply spectralTensor_mem_activitySubspace f
    intro i
    exact hrest i (by simp [hIempty])
  · exact activitySubspace_le_spectralWeightZero

/-- The activity space together with the positive spectral weights spans
the full state-vector space. -/
theorem activitySubspace_sup_positiveSpectralSubspace_eq_top :
    activitySubspace (A := A) (n := n) ⊔
      positiveSpectralSubspace (A := A) (n := n) = ⊤ := by
  have hle : spectralTotalSubspace (A := A) (n := n) ≤
      activitySubspace (A := A) (n := n) ⊔
        positiveSpectralSubspace (A := A) (n := n) := by
    unfold spectralTotalSubspace
    apply iSup_le
    intro l
    by_cases hl : l.val = 0
    · have hzero : spectralWeightSubspace (A := A) (n := n) l =
          activitySubspace (A := A) (n := n) := by
        simpa [hl] using (spectralWeightZero_eq_activitySubspace
          (A := A) (n := n))
      rw [hzero]
      exact le_sup_left
    · let j : Fin n := ⟨l.val - 1, by omega⟩
      have hj : j.val + 1 = l.val := by
        dsimp [j]
        omega
      have hpos : spectralWeightSubspace (A := A) (n := n) l ≤
          positiveSpectralSubspace (A := A) (n := n) := by
        change spectralWeightSubspace (A := A) (n := n) l.val ≤
          ⨆ k : Fin n,
            spectralWeightSubspace (A := A) (n := n) (k.val + 1)
        simpa [hj] using
          (le_iSup (fun k : Fin n =>
            spectralWeightSubspace (A := A) (n := n) (k.val + 1)) j)
      exact hpos.trans le_sup_right
  rw [spectralTotalSubspace_eq_top] at hle
  exact top_unique hle

/-- One complementary one-word factor makes a tensor orthogonal to every
activity-box indicator. -/
theorem activityBoxIndicator_dot_spectralTensor_eq_zero
    (z : Fin n → Bool) (I : Finset (Fin n)) (f : Fin n → A → ℝ)
    (hI : I.Nonempty)
    (hf : ∀ i ∈ I, InWordActivityOrthogonalComplement (f i)) :
    activityBoxIndicator (A := A) z ⬝ᵥ spectralTensor f = 0 := by
  rw [activityBoxIndicator_eq_spectralTensor, spectralTensor_dot]
  obtain ⟨i, hi⟩ := hI
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact hf i hi _ (activityWordVector_mem_wordActivitySubspace (z i))

/-- Every `W_l` with `l > 0` is orthogonal to each activity-box indicator. -/
theorem spectralWeightSubspace_dot_activityBox_eq_zero
    (l : ℕ) (hl : 0 < l) (w : State A n → ℝ)
    (hw : w ∈ spectralWeightSubspace (A := A) (n := n) l)
    (z : Fin n → Bool) :
    activityBoxIndicator z ⬝ᵥ w = 0 := by
  change w ∈ Submodule.span ℝ
    {v | ∃ (I : Finset (Fin n)) (f : Fin n → A → ℝ),
      I.card = l ∧
        (∀ i ∈ I, InWordActivityOrthogonalComplement (f i)) ∧
        (∀ i ∉ I, f i ∈ wordActivitySubspace (A := A)) ∧
        v = spectralTensor f} at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨I, f, hcard, horth, _, rfl⟩ := hv
      exact activityBoxIndicator_dot_spectralTensor_eq_zero z I f
        (Finset.card_pos.mp (by omega)) horth
  | zero => simp
  | add x y _ _ hx hy =>
      rw [dotProduct_add, hx, hy, add_zero]
  | smul t x _ hx =>
      simp [dotProduct_smul, hx]

/-- For `l > 0`, the paper's `W_l` lies in the algebraic orthogonal
complement of the activity subspace `V`. -/
theorem spectralWeightSubspace_mem_activityOrthogonalComplement
    (l : ℕ) (hl : 0 < l) (w : State A n → ℝ)
    (hw : w ∈ spectralWeightSubspace (A := A) (n := n) l) :
    InActivityOrthogonalComplement w := by
  intro v hv
  change v ∈ Submodule.span ℝ
    (Set.range (activityBoxIndicator (A := A) (n := n))) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact spectralWeightSubspace_dot_activityBox_eq_zero l hl w hw z
  | zero => simp
  | add x y _ _ hx hy =>
      rw [add_dotProduct, hx, hy, zero_add]
  | smul t x _ hx =>
      simp [smul_dotProduct, hx]

/-- Pure tensors with different sets of complementary word factors are
orthogonal. -/
theorem spectralTensor_dot_eq_zero_of_distinct_factorSets
    (I J : Finset (Fin n)) (hIJ : I ≠ J)
    (f g : Fin n → A → ℝ)
    (hforth : ∀ i ∈ I, InWordActivityOrthogonalComplement (f i))
    (hfact : ∀ i ∉ I, f i ∈ wordActivitySubspace (A := A))
    (hgorth : ∀ i ∈ J, InWordActivityOrthogonalComplement (g i))
    (hgact : ∀ i ∉ J, g i ∈ wordActivitySubspace (A := A)) :
    spectralTensor f ⬝ᵥ spectralTensor g = 0 := by
  have hdiff : ∃ i : Fin n,
      (i ∈ I ∧ i ∉ J) ∨ (i ∈ J ∧ i ∉ I) := by
    by_contra h
    have hleIJ : I ⊆ J := by
      intro i hi
      by_contra hj
      exact h ⟨i, Or.inl ⟨hi, hj⟩⟩
    have hleJI : J ⊆ I := by
      intro i hj
      by_contra hi
      exact h ⟨i, Or.inr ⟨hj, hi⟩⟩
    exact hIJ (Finset.Subset.antisymm hleIJ hleJI)
  obtain ⟨i, hi⟩ := hdiff
  rw [spectralTensor_dot]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with ⟨hiI, hiJ⟩ | ⟨hiJ, hiI⟩
  · rw [dotProduct_comm]
    exact hforth i hiI (g i) (hgact i hiJ)
  · exact hgorth i hiJ (f i) (hfact i hiI)

/-- The Gram matrix `B_lᵀ B_l` has zero entries between columns with
different complementary-position sets, exactly as in the paper. -/
theorem spectralBasisMatrix_gram_zero_of_distinct_positionSets
    (l : ℕ)
    (c d : SpectralBasisIndex (A := A) (n := n) l)
    (hcd : c.1.1 ≠ d.1.1) :
    ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l) c d = 0 := by
  classical
  rw [Matrix.mul_apply]
  change spectralTensor (fun i => if hi : i ∈ c.1.1 then
      wordComplementBasisVector (A := A) (c.2.1 ⟨i, hi⟩)
      else normalizedActivityWordVector (A := A) (c.2.2 ⟨i, hi⟩)) ⬝ᵥ
    spectralTensor (fun i => if hi : i ∈ d.1.1 then
      wordComplementBasisVector (A := A) (d.2.1 ⟨i, hi⟩)
      else normalizedActivityWordVector (A := A) (d.2.2 ⟨i, hi⟩)) = 0
  apply spectralTensor_dot_eq_zero_of_distinct_factorSets c.1.1 d.1.1 hcd
  · intro i hi
    simpa [hi] using (wordComplementBasisVector_orthogonal
      (A := A) (c.2.1 ⟨i, hi⟩))
  · intro i hi
    simpa [hi] using (normalizedActivityWordVector_mem_wordActivitySubspace
      (A := A) (c.2.2 ⟨i, hi⟩))
  · intro i hi
    simpa [hi] using (wordComplementBasisVector_orthogonal
      (A := A) (d.2.1 ⟨i, hi⟩))
  · intro i hi
    simpa [hi] using (normalizedActivityWordVector_mem_wordActivitySubspace
      (A := A) (d.2.2 ⟨i, hi⟩))

/-- Within a fixed position-set block, the Gram entries of the actual
`B_l` matrix are the paper's identity factors times the `2 × 2`
activity Gram factors. -/
theorem spectralBasisMatrix_gram_same_positionSet
    (l : ℕ) (I : {I : Finset (Fin n) // I.card = l})
    (j k : {i : Fin n // i ∈ I.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (z w : {i : Fin n // i ∉ I.1} → Bool) :
    ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l)
        ⟨I, (j, z)⟩ ⟨I, (k, w)⟩ =
      ∏ i : Fin n,
        if hi : i ∈ I.1 then
          (if j ⟨i, hi⟩ = k ⟨i, hi⟩ then (1 : ℝ) else 0)
        else if z ⟨i, hi⟩ = w ⟨i, hi⟩ then 1
        else (Real.sqrt (Fintype.card A : ℝ))⁻¹ := by
  classical
  rw [Matrix.mul_apply]
  change spectralTensor (fun i => if hi : i ∈ I.1 then
      wordComplementBasisVector (A := A) (j ⟨i, hi⟩)
      else normalizedActivityWordVector (A := A) (z ⟨i, hi⟩)) ⬝ᵥ
    spectralTensor (fun i => if hi : i ∈ I.1 then
      wordComplementBasisVector (A := A) (k ⟨i, hi⟩)
      else normalizedActivityWordVector (A := A) (w ⟨i, hi⟩)) = _
  rw [spectralTensor_dot]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ I.1
  · simp [hi, wordComplementBasisVector_dotProduct]
  · simp [hi, normalizedActivityWordVector_dotProduct]

section SpectralActivityGramKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized activity Gram kernel on an arbitrary finite set of word positions. -/
def spectralActivityGramKernel (r : ℝ) :
    Matrix (ι → Bool) (ι → Bool) ℝ :=
  fun x y => ∏ i : ι, if x i = y i then 1 else r

private theorem spectralActivityGramKernel_single_sum
    (r : ℝ) (a b : Bool) :
    (∑ z : Bool,
      (if a = z then (1 : ℝ) else r) *
        (if z = b then (1 : ℝ) else -r)) =
      if a = b then 1 - r ^ 2 else 0 := by
  cases a <;> cases b <;> simp <;> ring

theorem spectralActivityGramKernel_mul_negative (r : ℝ) :
    spectralActivityGramKernel (ι := ι) r *
      spectralActivityGramKernel (ι := ι) (-r) =
        (1 - r ^ 2) ^ (Fintype.card ι) •
          (1 : Matrix (ι → Bool) (ι → Bool) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, spectralActivityGramKernel,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  calc
    (∑ z : ι → Bool,
      (∏ i : ι, if x i = z i then (1 : ℝ) else r) *
        (∏ i : ι, if z i = y i then (1 : ℝ) else -r)) =
      ∑ z : ι → Bool,
        ∏ i : ι,
          (if x i = z i then (1 : ℝ) else r) *
            (if z i = y i then (1 : ℝ) else -r) := by
              simp only [Finset.prod_mul_distrib]
    _ = ∏ i : ι,
          ∑ z : Bool,
            (if x i = z then (1 : ℝ) else r) *
              (if z = y i then (1 : ℝ) else -r) := by
          simpa using (Finset.sum_prod_piFinset (s := Finset.univ)
            (g := fun i z =>
              (if x i = z then (1 : ℝ) else r) *
                (if z = y i then (1 : ℝ) else -r)))
    _ = (1 - r ^ 2) ^ (Fintype.card ι) * if x = y then 1 else 0 := by
      simp only [spectralActivityGramKernel_single_sum]
      by_cases hxy : x = y
      · subst y
        simp [Finset.prod_const]
      · have hbad : ∃ i : ι, x i ≠ y i := by
          by_contra h
          push_neg at h
          exact hxy (funext h)
        obtain ⟨i, hi⟩ := hbad
        simp only [if_neg hxy, mul_zero]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Hamming weight of an activity-bit pattern on an arbitrary finite set of word positions. -/
def spectralActivityWeight (z : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun i => z i = true)).card

/-- Coordinatewise symmetric difference of activity-bit patterns. -/
def spectralActivityXor (x y : ι → Bool) (i : ι) : Bool :=
  Bool.xor (x i) (y i)

omit [DecidableEq ι] in
/-- The activity Gram kernel is a power indexed by Hamming distance. -/
theorem spectralActivityGramKernel_coordinate (r : ℝ)
    (x y : ι → Bool) :
    spectralActivityGramKernel r x y =
      r ^ spectralActivityWeight (spectralActivityXor x y) := by
  have hw : spectralActivityWeight (spectralActivityXor x y) =
      ∑ i : ι, if x i = y i then 0 else 1 := by
    unfold spectralActivityWeight
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases hx : x i <;> cases hy : y i <;>
      simp [spectralActivityXor, hx, hy]
  rw [spectralActivityGramKernel, hw]
  have hterm (i : ι) :
      (if x i = y i then (1 : ℝ) else r) =
        r ^ (if x i = y i then 0 else 1) := by
    by_cases h : x i = y i <;> simp [h]
  simp_rw [hterm]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem spectralActivityGramKernel_negative_rowAbsSum
    (r : ℝ) (hr : 0 ≤ r) (x : ι → Bool) :
    (∑ y : ι → Bool,
      |spectralActivityGramKernel (ι := ι) (-r) x y|) =
        (1 + r) ^ (Fintype.card ι) := by
  have hentry (y : ι → Bool) :
      |spectralActivityGramKernel (ι := ι) (-r) x y| =
        spectralActivityGramKernel (ι := ι) r x y := by
    rw [spectralActivityGramKernel_coordinate,
      spectralActivityGramKernel_coordinate]
    simp [abs_pow, abs_neg, abs_of_nonneg hr]
  simp_rw [hentry]
  calc
    (∑ y : ι → Bool, spectralActivityGramKernel (ι := ι) r x y) =
        ∏ i : ι,
          ∑ b : Bool, if x i = b then (1 : ℝ) else r := by
        simpa only [spectralActivityGramKernel] using
          (Finset.sum_prod_piFinset (s := Finset.univ)
            (g := fun i b => if x i = b then (1 : ℝ) else r))
    _ = ∏ _i : ι, (1 + r) := by
      apply Finset.prod_congr rfl
      intro i _
      cases x i <;> simp [add_comm]
    _ = (1 + r) ^ (Fintype.card ι) := by simp

end SpectralActivityGramKernel

/-- A fixed-position Gram block of the paper's spectral basis matrix is an identity on complementary-basis choices times the normalized activity Gram kernel on the remaining word positions. -/
theorem spectralBasisMatrix_gram_same_positionSet_eq_activityKernel
    (l : ℕ) (I : {I : Finset (Fin n) // I.card = l})
    (j k : {i : Fin n // i ∈ I.1} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
    (z w : {i : Fin n // i ∉ I.1} → Bool) :
    ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l)
        ⟨I, (j, z)⟩ ⟨I, (k, w)⟩ =
      (if j = k then (1 : ℝ) else 0) *
        spectralActivityGramKernel (ι := {i : Fin n // i ∉ I.1})
          ((Real.sqrt (Fintype.card A : ℝ))⁻¹) z w := by
  classical
  letI : Fintype {i : Fin n // i ∈ I.1} := Subtype.fintype _
  letI : Fintype {i : Fin n // i ∉ I.1} := Subtype.fintype _
  rw [spectralBasisMatrix_gram_same_positionSet]
  let r : ℝ := (Real.sqrt (Fintype.card A : ℝ))⁻¹
  let h : Fin n → ℝ := fun i =>
    if hi : i ∈ I.1 then
      (if j ⟨i, hi⟩ = k ⟨i, hi⟩ then (1 : ℝ) else 0)
    else if z ⟨i, hi⟩ = w ⟨i, hi⟩ then 1 else r
  have hcomp : (∏ i : {i : Fin n // i ∈ I.1}, h i.1) =
      if j = k then (1 : ℝ) else 0 := by
    have hfac (i : {i : Fin n // i ∈ I.1}) :
        h i.1 = if j i = k i then (1 : ℝ) else 0 := by
      simp [h, i.2]
    simp_rw [hfac]
    simp [Fintype.prod_ite_zero, funext_iff]
  have hact : (∏ i : {i : Fin n // i ∉ I.1}, h i.1) =
      spectralActivityGramKernel (ι := {i : Fin n // i ∉ I.1}) r z w := by
    have hfac (i : {i : Fin n // i ∉ I.1}) :
        h i.1 = if z i = w i then (1 : ℝ) else r := by
      simp [h, i.2]
    simp_rw [hfac]
    rfl
  change (∏ i : Fin n, h i) = _
  calc
    (∏ i : Fin n, h i) =
        (∏ i : {i : Fin n // i ∈ I.1}, h i.1) *
          (∏ i : {i : Fin n // i ∉ I.1}, h i.1) :=
      (Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ I.1) h).symm
    _ = _ := by
      rw [hcomp, hact]
      by_cases hjk : j = k <;> simp [hjk, r]

/-- The complementary-basis and activity-bit choices within one fixed-position spectral Gram block. -/
abbrev SpectralGramBlockIndex (I : Finset (Fin n)) :=
  ({i : Fin n // i ∈ I} →
    Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
  ({i : Fin n // i ∉ I} → Bool)

/-- The fixed-position Gram kernel as the Kronecker product of the complementary identity and activity Gram kernel. -/
noncomputable def spectralGramBlockKernel (I : Finset (Fin n)) (r : ℝ) :
    Matrix (SpectralGramBlockIndex (A := A) I)
      (SpectralGramBlockIndex (A := A) I) ℝ :=
  Matrix.kronecker
    (1 : Matrix ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
      ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ℝ)
    (spectralActivityGramKernel (ι := {i : Fin n // i ∉ I}) r)

theorem spectralGramBlockKernel_apply
    (I : Finset (Fin n)) (r : ℝ)
    (x y : SpectralGramBlockIndex (A := A) I) :
    spectralGramBlockKernel (A := A) I r x y =
      (if x.1 = y.1 then (1 : ℝ) else 0) *
        spectralActivityGramKernel r x.2 y.2 := by
  classical
  exact Matrix.kronecker_apply _ _ _ _ _ _

/-- The fixed-position spectral Gram kernel has the paper's exact inverse: identity on complementary choices and the inverse activity Gram kernel. -/
theorem spectralGramBlockKernel_inverse
    (I : Finset (Fin n)) (r : ℝ) (hr : 1 - r ^ 2 ≠ 0) :
    (spectralGramBlockKernel (A := A) I r)⁻¹ =
      (((1 - r ^ 2) ^
          Fintype.card {i : Fin n // i ∉ I})⁻¹) •
        spectralGramBlockKernel (A := A) I (-r) := by
  classical
  let H := spectralActivityGramKernel (ι := {i : Fin n // i ∉ I}) r
  let K := spectralActivityGramKernel (ι := {i : Fin n // i ∉ I}) (-r)
  let J : Matrix ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
      ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ℝ := 1
  let t : ℝ := ((1 - r ^ 2) ^
    Fintype.card {i : Fin n // i ∉ I})⁻¹
  have hHK : H * (t • K) = 1 := by
    dsimp [H, K, t]
    rw [Matrix.mul_smul, spectralActivityGramKernel_mul_negative]
    rw [smul_smul]
    simp [hr]
  have hright : spectralGramBlockKernel (A := A) I r *
      (t • spectralGramBlockKernel (A := A) I (-r)) = 1 := by
    change Matrix.kroneckerMap (· * ·) J H *
      (t • Matrix.kroneckerMap (· * ·) J K) = 1
    rw [← Matrix.kronecker_smul t J K]
    rw [← Matrix.mul_kronecker_mul]
    rw [Matrix.one_mul]
    change Matrix.kronecker J (H * (t • K)) = 1
    rw [hHK]
    exact Matrix.one_kronecker_one
  exact Matrix.inv_eq_right_inv hright

/-- The actual `B_lᵀ B_l` submatrix at a fixed complementary-position set is the Kronecker Gram block. -/
theorem spectralBasisMatrix_gram_block_eq_kernel
    (l : ℕ) (I : {I : Finset (Fin n) // I.card = l}) :
    (((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l).submatrix
        (fun x : SpectralGramBlockIndex (A := A) I.1 =>
          (⟨I, x⟩ : SpectralBasisIndex (A := A) (n := n) l))
        (fun x : SpectralGramBlockIndex (A := A) I.1 =>
          (⟨I, x⟩ : SpectralBasisIndex (A := A) (n := n) l))) =
      spectralGramBlockKernel (A := A) I.1
        ((Real.sqrt (Fintype.card A : ℝ))⁻¹) := by
  classical
  ext x y
  rcases x with ⟨j,z⟩
  rcases y with ⟨k,w⟩
  rw [Matrix.submatrix_apply,
    spectralBasisMatrix_gram_same_positionSet_eq_activityKernel,
    spectralGramBlockKernel_apply]

/-- The paper's fixed-position Gram blocks, indexed by complementary-position sets. -/
noncomputable def spectralBasisMatrix_gramBlockFamily (l : ℕ)
    (I : {I : Finset (Fin n) // I.card = l}) :
    Matrix (SpectralGramBlockIndex (A := A) I.1)
      (SpectralGramBlockIndex (A := A) I.1) ℝ :=
  spectralGramBlockKernel (A := A) I.1
    ((Real.sqrt (Fintype.card A : ℝ))⁻¹)

/-- The full Gram matrix `B_lᵀB_l` is exactly the dependent block diagonal matrix of its fixed-position kernels. -/
theorem spectralBasisMatrix_gram_eq_blockDiagonal (l : ℕ) :
    (spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l =
      Matrix.blockDiagonal' (spectralBasisMatrix_gramBlockFamily (A := A) l) := by
  classical
  ext c d
  rcases c with ⟨I,x⟩
  rcases d with ⟨J,y⟩
  by_cases hIJ : I = J
  · subst J
    rw [Matrix.blockDiagonal'_apply_eq]
    have hb := spectralBasisMatrix_gram_block_eq_kernel (A := A) l I
    exact congrFun (congrFun hb x) y
  · rw [Matrix.blockDiagonal'_apply]
    simp only [dif_neg hIJ]
    apply spectralBasisMatrix_gram_zero_of_distinct_positionSets
    intro h
    apply hIJ
    exact Subtype.ext h

theorem spectralGramBlockKernel_mul_inverse
    (I : Finset (Fin n)) (r : ℝ) (hr : 1 - r ^ 2 ≠ 0) :
    spectralGramBlockKernel (A := A) I r *
      (spectralGramBlockKernel (A := A) I r)⁻¹ = 1 := by
  classical
  let H := spectralActivityGramKernel (ι := {i : Fin n // i ∉ I}) r
  let K := spectralActivityGramKernel (ι := {i : Fin n // i ∉ I}) (-r)
  let J : Matrix ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
      ({i : Fin n // i ∈ I} →
      Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ℝ := 1
  let t : ℝ := ((1 - r ^ 2) ^
    Fintype.card {i : Fin n // i ∉ I})⁻¹
  have hHK : H * (t • K) = 1 := by
    dsimp [H, K, t]
    rw [Matrix.mul_smul, spectralActivityGramKernel_mul_negative]
    rw [smul_smul]
    simp [hr]
  rw [spectralGramBlockKernel_inverse I r hr]
  change Matrix.kroneckerMap (· * ·) J H *
    (t • Matrix.kroneckerMap (· * ·) J K) = 1
  rw [← Matrix.kronecker_smul t J K]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.one_mul]
  change Matrix.kronecker J (H * (t • K)) = 1
  rw [hHK]
  exact Matrix.one_kronecker_one

/-- The exact inverse of the full paper-style spectral Gram matrix, assembled from the inverses of its fixed-position blocks. -/
theorem spectralBasisMatrix_gram_inverse
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    (((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l)⁻¹) =
      Matrix.blockDiagonal'
        (fun I : {I : Finset (Fin n) // I.card = l} =>
          (spectralBasisMatrix_gramBlockFamily (A := A) l I)⁻¹) := by
  classical
  let r : ℝ := (Real.sqrt (Fintype.card A : ℝ))⁻¹
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩
  have hq : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
  have hsqrt : 1 < Real.sqrt (Fintype.card A : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity)).mpr hsqrt
  have hr : 1 - r ^ 2 ≠ 0 := by
    have hsq : r ^ 2 < 1 := by nlinarith
    exact ne_of_gt (sub_pos.mpr hsq)
  have hblock (I : {I : Finset (Fin n) // I.card = l}) :
      spectralBasisMatrix_gramBlockFamily (A := A) l I *
        (spectralBasisMatrix_gramBlockFamily (A := A) l I)⁻¹ = 1 := by
    exact spectralGramBlockKernel_mul_inverse I.1 r hr
  rw [spectralBasisMatrix_gram_eq_blockDiagonal]
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.blockDiagonal'_mul]
  simp_rw [hblock]
  exact Matrix.blockDiagonal'_one

/-- For distinct spectral weights, a pure tensor generator of `W_l` is
orthogonal to all of `W_k`. -/
private theorem spectralTensor_dot_spectralWeightSubspace_eq_zero
    (I : Finset (Fin n)) (f : Fin n → A → ℝ)
    (hforth : ∀ i ∈ I, InWordActivityOrthogonalComplement (f i))
    (hfact : ∀ i ∉ I, f i ∈ wordActivitySubspace (A := A))
    (k : ℕ) (hcard : I.card ≠ k)
    (w : State A n → ℝ)
    (hw : w ∈ spectralWeightSubspace (A := A) (n := n) k) :
    spectralTensor f ⬝ᵥ w = 0 := by
  change w ∈ Submodule.span ℝ
    {v | ∃ (J : Finset (Fin n)) (g : Fin n → A → ℝ),
      J.card = k ∧
        (∀ i ∈ J, InWordActivityOrthogonalComplement (g i)) ∧
        (∀ i ∉ J, g i ∈ wordActivitySubspace (A := A)) ∧
        v = spectralTensor g} at hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨J, g, hJcard, hgorth, hgact, rfl⟩ := hv
      apply spectralTensor_dot_eq_zero_of_distinct_factorSets I J
      · intro hIJ
        exact hcard (by rw [hIJ, hJcard])
      · exact hforth
      · exact hfact
      · exact hgorth
      · exact hgact
  | zero => simp
  | add x y _ _ hx hy =>
      rw [dotProduct_add, hx, hy, add_zero]
  | smul t x _ hx =>
      simp [dotProduct_smul, hx]

/-- The paper's spaces `W_l` are pairwise orthogonal for distinct weights. -/
theorem spectralWeightSubspaces_orthogonal
    (l k : ℕ) (hlk : l ≠ k)
    (v w : State A n → ℝ)
    (hv : v ∈ spectralWeightSubspace (A := A) (n := n) l)
    (hw : w ∈ spectralWeightSubspace (A := A) (n := n) k) :
    v ⬝ᵥ w = 0 := by
  change v ∈ Submodule.span ℝ
    {u | ∃ (I : Finset (Fin n)) (f : Fin n → A → ℝ),
      I.card = l ∧
        (∀ i ∈ I, InWordActivityOrthogonalComplement (f i)) ∧
        (∀ i ∉ I, f i ∈ wordActivitySubspace (A := A)) ∧
        u = spectralTensor f} at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨I, f, hIcard, hforth, hfact, rfl⟩ := hv
      apply spectralTensor_dot_spectralWeightSubspace_eq_zero I f hforth hfact k
      · intro hIk
        exact hlk (hIcard.symm.trans hIk)
      · exact hw
  | zero => simp
  | add x y _ _ hx hy =>
      rw [add_dotProduct, hx, hy, zero_add]
  | smul t x _ hx =>
      simp [smul_dotProduct, hx]

/-- The paper's full spectral decomposition of the activity orthogonal
complement: `V⊥ = W₁ ⊕ ⋯ ⊕ Wₙ`. Pairwise orthogonality of the summands is
`spectralWeightSubspaces_orthogonal`. -/
theorem positiveSpectralSubspace_eq_activityOrthogonalSubspace :
    positiveSpectralSubspace (A := A) (n := n) =
      activityAlgebraicOrthogonalSubspace (A := A) (n := n) := by
  let V := activitySubspace (A := A) (n := n)
  let P := positiveSpectralSubspace (A := A) (n := n)
  let Q := activityAlgebraicOrthogonalSubspace (A := A) (n := n)
  have hPQ : P ≤ Q := by
    unfold P positiveSpectralSubspace
    apply iSup_le
    intro l w hw
    exact spectralWeightSubspace_mem_activityOrthogonalComplement
      (l.val + 1) (by omega) w hw
  apply le_antisymm hPQ
  intro w hw
  have hsup : w ∈ V ⊔ P := by
    rw [show V ⊔ P = ⊤ from
      activitySubspace_sup_positiveSpectralSubspace_eq_top]
    trivial
  obtain ⟨v, hv, p, hp, hvp⟩ := Submodule.mem_sup.mp hsup
  have hvQ : v ∈ Q := by
    have hwp : v + p ∈ Q := by rw [hvp]; exact hw
    have hvform : v = (v + p) - p := by abel
    rw [hvform]
    exact Q.sub_mem hwp (hPQ hp)
  have hvK : WithLp.toLp 2 v ∈
      activityHilbertSubspace (A := A) (n := n) :=
    (mem_activityHilbertSubspace_iff (WithLp.toLp 2 v)).2 (by simpa using hv)
  have hvKorth : WithLp.toLp 2 v ∈
      (activityHilbertSubspace (A := A) (n := n))ᗮ :=
    (inActivityOrthogonalComplement_iff_mem_orthogonal
      (WithLp.toLp 2 v)).1 (by simpa [Q, activityAlgebraicOrthogonalSubspace] using hvQ)
  have hvzeroHilbert : (WithLp.toLp 2 v : EuclideanSpace ℝ (State A n)) = 0 := by
    have hboth : WithLp.toLp 2 v ∈
        activityHilbertSubspace (A := A) (n := n) ⊓
          (activityHilbertSubspace (A := A) (n := n))ᗮ := ⟨hvK, hvKorth⟩
    rw [(activityHilbertSubspace (A := A) (n := n)).inf_orthogonal_eq_bot] at hboth
    simpa using hboth
  have hvzero : v = 0 := by
    have h := congrArg (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) hvzeroHilbert
    simpa using h
  have hpw : p = w := by simpa [hvzero] using hvp
  rw [← hpw]
  exact hp

/-- Membership in the positive spectral sum is exactly membership in the
Hilbert-space `V⊥` used by the three spectral block operators. -/
theorem mem_positiveSpectralSubspace_iff_mem_activityHilbertOrthogonal
    (w : EuclideanSpace ℝ (State A n)) :
    (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w ∈
      positiveSpectralSubspace (A := A) (n := n) ↔
      w ∈ (activityHilbertSubspace (A := A) (n := n))ᗮ := by
  rw [positiveSpectralSubspace_eq_activityOrthogonalSubspace]
  exact inActivityOrthogonalComplement_iff_mem_orthogonal w

/-- Distinct spectral weights are orthogonal for the Euclidean inner
product, not only the coordinate dot product. -/
theorem spectralWeightSubspaces_euclidean_orthogonal
    (l k : ℕ) (hlk : l ≠ k)
    (v w : EuclideanSpace ℝ (State A n))
    (hv : (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v ∈
      spectralWeightSubspace (A := A) (n := n) l)
    (hw : (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w ∈
      spectralWeightSubspace (A := A) (n := n) k) :
    ⟪v, w⟫ = 0 := by
  rw [euclidean_inner_eq_dotProduct]
  exact spectralWeightSubspaces_orthogonal l k hlk _ _ hv hw

/-! The one-word substitution matrix has the two fixed activity directions
identified in the paper's singular-value lemma. This also gives invariance
of their orthogonal complement for the matrix and its transpose. -/

/-- The coordinatewise tensor power of a one-word matrix. -/
def tensorWordMatrix (D : Matrix A A ℝ) :
    Matrix (State A n) (State A n) ℝ :=
  fun b a => ∏ i : Fin n, D (b i) (a i)

omit [AddCommGroup A] [DecidableEq A] in
/-- A tensor-product matrix acts on a pure tensor one word at a time. -/
theorem tensorWordMatrix_mulVec_spectralTensor
    (D : Matrix A A ℝ) (f : Fin n → A → ℝ) :
    tensorWordMatrix (n := n) D *ᵥ spectralTensor f =
      spectralTensor (fun i => D *ᵥ f i) := by
  funext b
  change (∑ a : State A n,
    (∏ i : Fin n, D (b i) (a i)) *
      (∏ i : Fin n, f i (a i))) =
    ∏ i : Fin n, ∑ a : A, D (b i) a * f i a
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (Finset.prod_mul_distrib).symm

/-- Independent word coordinates make the parallel S-box's differential
count the product of its one-word differential counts. -/
theorem substitute_differenceCount_eq_prod
    (S : A ≃ A) (b a : State A n) :
    differenceCount (substitute S : State A n → State A n) b a =
      ∏ i : Fin n, differenceCount (fun x : A => S x) (b i) (a i) := by
  classical
  change (∑ x : State A n,
    if substitute S (x + a) = substitute S x + b then 1 else 0) =
    ∏ i : Fin n, ∑ x : A,
      if S (x + a i) = S x + b i then 1 else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hiff : substitute S (x + a) = substitute S x + b ↔
      ∀ i : Fin n, S (x i + a i) = S (x i) + b i := by
    simp [substitute, funext_iff, Pi.add_apply]
  simp only [hiff]
  simp [Fintype.prod_ite_zero]

/-- The actual difference-distribution matrix of parallel substitution is
the tensor power of the one-word difference-distribution matrix. -/
theorem substitute_differenceDistributionMatrix_eq_tensorWordMatrix
    (S : A ≃ A) :
    deterministicDifferenceDistributionMatrix
      (substitute S : State A n → State A n) =
    tensorWordMatrix (n := n)
      (deterministicDifferenceDistributionMatrix (fun a : A => S a)) := by
  ext b a
  simp only [deterministicDifferenceDistributionMatrix,
    differenceDistributionMatrix_eq_count, Fintype.sum_unique,
    Fintype.card_unit, tensorWordMatrix]
  rw [substitute_differenceCount_eq_prod]
  simp only [Fintype.card_pi_const, Nat.cast_pow, Nat.cast_prod]
  rw [Finset.prod_div_distrib]
  simp

/-- A word vector is orthogonal to the paper's two activity directions
exactly when its zero coordinate and its total coordinate sum vanish. These
are the two cancellations used in the MDS vanishing argument. -/
theorem inWordActivityOrthogonalComplement_iff_zero_and_sum
    (v : A → ℝ) :
    InWordActivityOrthogonalComplement v ↔
      v 0 = 0 ∧ (∑ a : A, v a) = 0 := by
  constructor
  · intro hv
    have hzero := hv (wordZeroIndicator (A := A))
      (Submodule.subset_span (by simp))
    have hall := hv (wordAllIndicator (A := A))
      (Submodule.subset_span (by simp))
    constructor
    · simpa [wordZeroIndicator, dotProduct] using hzero
    · simpa [wordAllIndicator, dotProduct] using hall
  · rintro ⟨hzero, hsum⟩ g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · rw [hx]
          simpa [wordZeroIndicator, dotProduct] using hzero
        · rw [hx]
          simpa [wordAllIndicator, dotProduct] using hsum
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, zero_add]
    | smul t x _ hx => simp [smul_dotProduct, hx]

/-- Each of the paper's complementary basis vectors vanishes at the
zero difference. -/
theorem wordComplementBasisVector_zero
    (j : Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)) :
    wordComplementBasisVector (A := A) j 0 = 0 :=
  (inWordActivityOrthogonalComplement_iff_zero_and_sum _).mp
    (wordComplementBasisVector_orthogonal j) |>.1

/-- The complementary-basis completeness kernel vanishes when either
difference is zero. -/
theorem wordComplementBasisKernel_zero_left (b : A) :
    wordComplementBasisKernel (A := A) 0 b = 0 := by
  simp [wordComplementBasisKernel, wordComplementBasisVector_zero]

theorem wordComplementBasisKernel_zero_right (a : A) :
    wordComplementBasisKernel (A := A) a 0 = 0 := by
  simp [wordComplementBasisKernel, wordComplementBasisVector_zero]

/-- The paper's completeness identity for the `q - 2` complementary
one-word basis vectors, restricted to nonzero differences:
`∑_j v_j(a) v_j(b) = δ_{a,b} - 1/(q-1)`. -/
theorem wordComplementBasisKernel_nonzero (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    wordComplementBasisKernel (A := A) a b =
      (if a = b then (1 : ℝ) else 0) -
        ((Fintype.card A : ℝ) - 1)⁻¹ := by
  let c : ℝ := ((Fintype.card A : ℝ) - 1)⁻¹
  let u : A → ℝ := c •
    (wordAllIndicator (A := A) - wordZeroIndicator (A := A))
  let e : A → ℝ := Pi.single b (1 : ℝ)
  let K := wordActivityHilbertSubspace (A := A)
  let Q := Kᗮ
  have hcard : 2 ≤ Fintype.card A := by
    have hi : Function.Injective (fun i : Bool => if i then b else (0 : A)) := by
      intro i j h
      cases i <;> cases j <;> simp_all
    simpa using Fintype.card_le_of_injective _ hi
  have hc : ((Fintype.card A : ℝ) - 1) * c = 1 := by
    have hn : (Fintype.card A : ℝ) - 1 ≠ 0 := by
      have hcardreal : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
      linarith
    simp [c, hn]
  have humem : u ∈ wordActivitySubspace (A := A) := by
    apply (wordActivitySubspace (A := A)).smul_mem
    exact (wordActivitySubspace (A := A)).sub_mem
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have huK : WithLp.toLp 2 u ∈ K :=
    (mem_wordActivityHilbertSubspace_iff _).mpr (by simpa using humem)
  have hsumu : (∑ x : A, u x) = 1 := by
    simp only [u, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    rw [← Finset.mul_sum]
    have hs :
        (∑ x : A, (wordAllIndicator (A := A) x -
          wordZeroIndicator (A := A) x)) =
          (Fintype.card A : ℝ) - 1 := by
      simp [wordAllIndicator, Finset.sum_sub_distrib, wordZeroIndicator]
    rw [hs]
    simpa [mul_comm] using hc
  have hQfun : InWordActivityOrthogonalComplement (e - u) := by
    apply (inWordActivityOrthogonalComplement_iff_zero_and_sum _).mpr
    constructor
    · simp [e, u, hb, wordAllIndicator, wordZeroIndicator]
    · simp [Finset.sum_sub_distrib, e, hsumu]
  have hQ : WithLp.toLp 2 (e - u) ∈ Q :=
    (inWordActivityOrthogonalComplement_iff_mem_orthogonal _).mp
      (by simpa using hQfun)
  have hproj : Q.starProjection (WithLp.toLp 2 e) =
      WithLp.toLp 2 (e - u) := by
    apply Q.eq_starProjection_of_mem_orthogonal' hQ
      (K.le_orthogonal_orthogonal huK)
    ext x
    simp [e, Pi.single_apply, eq_comm]
  rw [wordComplementBasisKernel_eq_projection]
  have hp : ((Q.orthogonalProjection (WithLp.toLp 2 e) : Q) :
      EuclideanSpace ℝ A) = WithLp.toLp 2 (e - u) := hproj
  rw [show Pi.single b (1 : ℝ) = e from rfl, hp]
  simp [e, u, ha, wordAllIndicator, wordZeroIndicator, c]

/-- Every factor in the paper's complementary-basis kernel product has
absolute value at most one. -/
theorem wordComplementBasisKernel_abs_le_one (a b : A) :
    |wordComplementBasisKernel (A := A) a b| ≤ 1 := by
  by_cases ha : a = 0
  · subst a
    simp [wordComplementBasisKernel_zero_left]
  by_cases hb : b = 0
  · subst b
    simp [wordComplementBasisKernel_zero_right]
  have hcard : 2 ≤ Fintype.card A := by
    have h := Fintype.one_lt_card_iff.mpr
      (⟨0, a, Ne.symm ha⟩ : ∃ x y : A, x ≠ y)
    omega
  have hq : (1 : ℝ) ≤ (Fintype.card A : ℝ) - 1 := by
    have hcardreal : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
    linarith
  have hc0 : 0 ≤ ((Fintype.card A : ℝ) - 1)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  have hc1 : ((Fintype.card A : ℝ) - 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hq
  rw [wordComplementBasisKernel_nonzero a b ha hb]
  by_cases hab : a = b
  · simp only [if_pos hab]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [if_neg hab, zero_sub, abs_neg]
    simpa [abs_of_nonneg hc0] using hc1

/-- Distinct nonzero coordinates contribute exactly `1/(q-1)` in
absolute value, the factor counted in the paper's Frobenius estimate. -/
theorem wordComplementBasisKernel_abs_of_distinct_nonzero
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    |wordComplementBasisKernel (A := A) a b| =
      ((Fintype.card A : ℝ) - 1)⁻¹ := by
  have hcard : 2 ≤ Fintype.card A := by
    have h := Fintype.one_lt_card_iff.mpr
      (⟨0, a, Ne.symm ha⟩ : ∃ x y : A, x ≠ y)
    omega
  have hcardreal : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
  rw [wordComplementBasisKernel_nonzero a b ha hb]
  simp [hab, abs_of_nonneg (inv_nonneg.mpr (by linarith :
    0 ≤ (Fintype.card A : ℝ) - 1))]

omit [AddCommGroup A] in
private theorem wordComplementBasisKernel_rowMajorant_sum
    (a : A) (c : ℝ) :
    (∑ b : A, if a = b then (1 : ℝ) else c) =
      1 + ((Fintype.card A : ℝ) - 1) * c := by
  classical
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  have hsingleton : (Finset.univ.filter (fun b : A => a = b)) = {a} := by
    ext b
    simp [eq_comm]
  have hrest : (Finset.univ.filter (fun b : A => ¬ a = b)) =
      Finset.univ.erase a := by
    ext b
    simp [eq_comm]
  rw [hsingleton, hrest]
  have hcard : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  simp [Finset.card_erase_of_mem, Nat.cast_sub hcard]

/-- For each nonzero difference, the absolute row sum of the
complementary-basis kernel is at most two. -/
theorem wordComplementBasisKernel_abs_row_sum_le_two
    (a : A) (ha : a ≠ 0) :
    (∑ b : A, |wordComplementBasisKernel (A := A) a b|) ≤ 2 := by
  let c : ℝ := ((Fintype.card A : ℝ) - 1)⁻¹
  have hcard : 2 ≤ Fintype.card A := by
    have h := Fintype.one_lt_card_iff.mpr
      (⟨0, a, Ne.symm ha⟩ : ∃ x y : A, x ≠ y)
    omega
  have hq : (1 : ℝ) ≤ (Fintype.card A : ℝ) - 1 := by
    have hcardreal : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
    linarith
  have hc0 : 0 ≤ c := inv_nonneg.mpr (by linarith)
  have hcprod : ((Fintype.card A : ℝ) - 1) * c = 1 := by
    have hn : (Fintype.card A : ℝ) - 1 ≠ 0 := by linarith
    simp [c, hn]
  calc
    (∑ b : A, |wordComplementBasisKernel (A := A) a b|) ≤
        ∑ b : A, if a = b then (1 : ℝ) else c := by
      apply Finset.sum_le_sum
      intro b hbmem
      by_cases hab : a = b
      · simpa [hab] using wordComplementBasisKernel_abs_le_one
          (A := A) a b
      · by_cases hb : b = 0
        · subst b
          simp [hab, c, hc0, wordComplementBasisKernel_zero_right]
        · simpa [hab, c] using le_of_eq
            (wordComplementBasisKernel_abs_of_distinct_nonzero a b ha hb hab)
    _ = 1 + ((Fintype.card A : ℝ) - 1) * c :=
      wordComplementBasisKernel_rowMajorant_sum a c
    _ = 2 := by rw [hcprod]; ring

/-- The total absolute mass of the one-word complementary kernel is at
most `2(q-1)`. It is the one-coordinate count behind the paper's
`2^d(q-1)^d` aggregate estimate. -/
theorem wordComplementBasisKernel_abs_total_le :
    (∑ a : A, ∑ b : A,
      |wordComplementBasisKernel (A := A) a b|) ≤
      2 * ((Fintype.card A : ℝ) - 1) := by
  have hzero : (∑ b : A,
      |wordComplementBasisKernel (A := A) (0 : A) b|) = 0 := by
    simp [wordComplementBasisKernel_zero_left]
  have hsum := Finset.sum_le_card_nsmul
    ((Finset.univ : Finset A).erase 0)
    (fun a => ∑ b : A, |wordComplementBasisKernel (A := A) a b|)
    (2 : ℝ) (by
      intro a ha
      exact wordComplementBasisKernel_abs_row_sum_le_two a
        (Finset.ne_of_mem_erase ha))
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset A)
    (fun a => ∑ b : A, |wordComplementBasisKernel (A := A) a b|)
    (Finset.mem_univ (0 : A))
  change (∑ b : A, |wordComplementBasisKernel (A := A) 0 b|) +
      (∑ a ∈ (Finset.univ : Finset A).erase 0,
        ∑ b : A, |wordComplementBasisKernel (A := A) a b|) =
      ∑ a : A, ∑ b : A, |wordComplementBasisKernel (A := A) a b| at hsplit
  rw [hzero, zero_add] at hsplit
  rw [hsplit] at hsum
  have hcard : 1 ≤ Fintype.card A :=
    Fintype.card_pos_iff.mpr ⟨(0 : A)⟩
  simpa [Finset.card_erase_of_mem, Nat.cast_sub hcard, nsmul_eq_mul,
    mul_comm] using hsum

omit [AddCommGroup A] [DecidableEq A] in
private theorem pair_product_sum_finite
    {J : Type*} [Fintype J] [DecidableEq J]
    (w : A → A → ℝ) :
    (∑ x : J → A, ∑ y : J → A,
      ∏ i : J, w (x i) (y i)) =
      (∑ a : A, ∑ b : A, w a b) ^ Fintype.card J := by
  simp_rw [← Fintype.prod_sum]
  rw [← Fintype.prod_sum (fun (_i : J) (a : A) => ∑ b : A, w a b)]
  simp

/-- The same free-pair kernel bound with any finite set of coordinate
labels, used for a selected subset of MDS graph coordinates. -/
theorem wordComplementBasisKernel_abs_free_pairs_le_finite
    {J : Type*} [Fintype J] [DecidableEq J] :
    (∑ x : J → A, ∑ y : J → A,
      ∏ i : J,
        |wordComplementBasisKernel (A := A) (x i) (y i)|) ≤
      2 ^ Fintype.card J *
        ((Fintype.card A : ℝ) - 1) ^ Fintype.card J := by
  rw [pair_product_sum_finite (w := fun a b =>
    |wordComplementBasisKernel (A := A) a b|)]
  have hnonneg : 0 ≤
      (∑ a : A, ∑ b : A,
        |wordComplementBasisKernel (A := A) a b|) := by
    apply Finset.sum_nonneg
    intro a ha
    exact Finset.sum_nonneg (fun b hb => abs_nonneg _)
  simpa [mul_pow] using
    (pow_le_pow_left₀ hnonneg
      (wordComplementBasisKernel_abs_total_le (A := A))
      (Fintype.card J))

private theorem sum_pairs_le_full_of_injective
    {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype Y]
    (C : Finset X) (p : X → Y)
    (hp : ∀ x ∈ C, ∀ y ∈ C, p x = p y → x = y)
    (f : X → X → ℝ) (g : Y → Y → ℝ)
    (hfg : ∀ x ∈ C, ∀ y ∈ C, f x y ≤ g (p x) (p y))
    (hg : ∀ u v, 0 ≤ g u v) :
    (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
      ∑ u : Y, ∑ v : Y, g u v := by
  have hsum (F : Y → ℝ) :
      (∑ u ∈ C.image p, F u) = ∑ x ∈ C, F (p x) := by
    exact Finset.sum_image (fun x hx y hy h => hp x hx y hy h)
  calc
    (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
        ∑ x ∈ C, ∑ y ∈ C, g (p x) (p y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact hfg x hx y hy
    _ = ∑ u ∈ C.image p, ∑ v ∈ C.image p, g u v := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsum]
    _ ≤ ∑ u : Y, ∑ v : Y, g u v := by
      calc
        (∑ u ∈ C.image p, ∑ v ∈ C.image p, g u v) ≤
            ∑ u ∈ C.image p, ∑ v : Y, g u v := by
          apply Finset.sum_le_sum
          intro u hu
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro v hv hnot
          exact hg u v
        _ ≤ ∑ u : Y, ∑ v : Y, g u v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro u hu hnot
          exact Finset.sum_nonneg (fun v hv => hg u v)

private theorem product_subset_le_of_nonneg_of_le_one
    {J : Type*} [DecidableEq J]
    (S T : Finset J) (hST : S ⊆ T) (f : J → ℝ)
    (hf0 : ∀ i ∈ T, 0 ≤ f i) (hf1 : ∀ i ∈ T, f i ≤ 1) :
    (∏ i ∈ T, f i) ≤ ∏ i ∈ S, f i := by
  rw [← Finset.prod_sdiff hST]
  have hS0 : 0 ≤ ∏ i ∈ S, f i :=
    Finset.prod_nonneg (fun i hi => hf0 i (hST hi))
  have hrest : (∏ i ∈ T \ S, f i) ≤ 1 := by
    calc
      (∏ i ∈ T \ S, f i) ≤ ∏ i ∈ T \ S, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact hf0 i (Finset.sdiff_subset hi)
        · intro i hi
          exact hf1 i (Finset.sdiff_subset hi)
      _ = 1 := by simp
  simpa [mul_comm] using mul_le_of_le_one_right hS0 hrest

private theorem sum_of_squares_eq_pairwise_sum
    {J X : Type*} [Fintype J] [DecidableEq X]
    (C : Finset X) (f : J → X → ℝ) :
    (∑ j : J, (∑ x ∈ C, f j x) ^ 2) =
      ∑ x ∈ C, ∑ y ∈ C, ∑ j : J, f j x * f j y := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext x
  rw [Finset.sum_comm]

/-- The complementary-basis product identity with an arbitrary finite
set of coordinate labels, including the `2n` positions of an MDS
input-output graph. -/
theorem wordComplementBasisKernel_sum_product_finite
    {J : Type*} [Fintype J] [DecidableEq J]
    (x y : J → A) :
    (∑ j : (J → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      ∏ i : J,
        wordComplementBasisVector (A := A) (j i) (x i) *
          wordComplementBasisVector (A := A) (j i) (y i)) =
      ∏ i : J, wordComplementBasisKernel (A := A) (x i) (y i) := by
  simpa only [wordComplementBasisKernel, Fintype.piFinset_univ] using
    (Finset.sum_prod_piFinset
      (s := (Finset.univ : Finset
        (Fin (Module.finrank ℝ
          (wordActivityHilbertSubspace (A := A))ᗮ))))
      (g := fun (i : J) j =>
        wordComplementBasisVector (A := A) j (x i) *
          wordComplementBasisVector (A := A) j (y i)))

/-- The exact squared-sum expansion for arbitrary finite coordinate
labels and any finite codeword set. -/
theorem wordComplementBasisKernel_sum_squares_finite
    {J X : Type*} [Fintype J] [DecidableEq J] [DecidableEq X]
    (C : Finset X) (coord : X → J → A) :
    (∑ j : (J → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      (∑ x ∈ C, ∏ i : J,
        wordComplementBasisVector (A := A) (j i) (coord x i)) ^ 2) =
    ∑ x ∈ C, ∑ y ∈ C,
      ∏ i : J, wordComplementBasisKernel (A := A)
        (coord x i) (coord y i) := by
  rw [sum_of_squares_eq_pairwise_sum]
  simp_rw [← Finset.prod_mul_distrib]
  simp_rw [wordComplementBasisKernel_sum_product_finite]

/-- For a linear layer the difference-distribution matrix is a permutation
matrix, so its pairing is a single sum over input differences. -/
theorem linear_differenceDistributionMatrix_pairing_eq_sum
    (L : State A n ≃+ State A n) (v w : State A n → ℝ) :
    w ⬝ᵥ deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a) *ᵥ v =
      ∑ a : State A n, w (L a) * v a := by
  change (∑ b : State A n, w b *
    ∑ a : State A n,
      deterministicDifferenceDistributionMatrix
        (fun x : State A n => L x) b a * v a) = _
  have hL (b a : State A n) :
      deterministicDifferenceDistributionMatrix
        (fun x : State A n => L x) b a =
          if L a = b then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom b a
  simp_rw [hL]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- A coordinate of the paper's `B_{l₁}ᵀ D_L B_{l₂}` matrix is a sum
over MDS graph codewords. This is the entry formula used before the
paper groups coordinates by zero indicators and complementary factors. -/
theorem spectralBasisMatrix_linear_innerProduct_eq_graph_sum
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) =
      ∑ a : State A n,
        spectralBasisMatrix (A := A) (n := n) l₁ (L a) c *
          spectralBasisMatrix (A := A) (n := n) l₂ a d := by
  have hentry :
      (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
        deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *
        spectralBasisMatrix (A := A) (n := n) l₂) c d) =
      (fun b => spectralBasisMatrix (A := A) (n := n) l₁ b c) ⬝ᵥ
        deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *ᵥ
            (fun a => spectralBasisMatrix (A := A) (n := n) l₂ a d) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [hentry]
  exact linear_differenceDistributionMatrix_pairing_eq_sum L _ _

/-- A codeword in the graph of the MDS linear layer, indexed by its input
and output word positions. -/
def mdsGraphCoordinate (L : State A n ≃+ State A n)
    (a : State A n) : Sum (Fin n) (Fin n) → A :=
  Sum.elim a (L a)

/-- The product of the two `B_l` column entries is precisely the
product of their `2n` word factors evaluated on an MDS graph codeword. -/
theorem spectralBasisMatrix_graphFactor_product
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (a : State A n) :
    spectralBasisMatrix (A := A) (n := n) l₁ (L a) c *
      spectralBasisMatrix (A := A) (n := n) l₂ a d =
    ∏ j : Sum (Fin n) (Fin n),
      spectralBasisGraphFactor l₁ l₂ c d j
        (mdsGraphCoordinate L a j) := by
  rw [Fintype.prod_sum_type]
  change (∏ i : Fin n, spectralBasisWordFactor l₁ c i ((L a) i)) *
      (∏ i : Fin n, spectralBasisWordFactor l₂ d i (a i)) =
    (∏ i : Fin n, spectralBasisWordFactor l₂ d i (a i)) *
      (∏ i : Fin n, spectralBasisWordFactor l₁ c i ((L a) i))
  exact mul_comm _ _

/-- A coordinate of `B_{l₁}ᵀ D_L B_{l₂}` as the product-sum over
all `2n` graph positions used in the paper's Frobenius proof. -/
theorem spectralBasisMatrix_linear_innerProduct_eq_graphProductSum
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) =
      ∑ a : State A n,
        ∏ j : Sum (Fin n) (Fin n),
          spectralBasisGraphFactor l₁ l₂ c d j
            (mdsGraphCoordinate L a j) := by
  rw [spectralBasisMatrix_linear_innerProduct_eq_graph_sum]
  simp_rw [spectralBasisMatrix_graphFactor_product]

/-- The `k ≥ n` case of the paper's MDS vanishing argument: if input and
output tensors are supported on activity boxes whose weights total at most
`n`, only the zero difference survives, and one complementary word factor
makes that term vanish. -/
theorem linear_differenceDistributionMatrix_pairing_zero_of_low_activity_support
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) (hweight : activityWeight x + activityWeight y ≤ n)
    (v w : State A n → ℝ)
    (hv : ∀ a, ¬ InActivityBox x a → v a = 0)
    (hw : ∀ b, ¬ InActivityBox y b → w b = 0)
    (hzero : v 0 = 0 ∨ w 0 = 0) :
    w ⬝ᵥ deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a) *ᵥ v = 0 := by
  rw [linear_differenceDistributionMatrix_pairing_eq_sum]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : InActivityBox x a
  · by_cases hb : InActivityBox y (L a)
    · have hazero := hMDS.eq_zero_of_activityBoxes L x y a ha hb hweight
      subst a
      rcases hzero with hz | hz
      · simp [hz]
      · simp [hz]
    · simp [hw (L a) hb]
  · simp [hv a ha]

omit [Fintype A] in
/-- A pure tensor whose inactive word factors equal `δ₀` is supported on
the corresponding activity box. -/
theorem spectralTensor_zero_outside_activityBox
    (z : Fin n → Bool) (f : Fin n → A → ℝ)
    (hf : ∀ i, z i = false → f i = wordZeroIndicator (A := A))
    (a : State A n) (ha : ¬ InActivityBox z a) :
    spectralTensor f a = 0 := by
  unfold InActivityBox at ha
  push_neg at ha
  obtain ⟨i, hzi, hai⟩ := ha
  unfold spectralTensor
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hf i hzi, wordZeroIndicator, hai]

/-- A pure tensor with one factor in the one-word activity complement
vanishes at the zero state. -/
theorem spectralTensor_zero_of_orthogonal_factor
    (f : Fin n → A → ℝ) (i : Fin n)
    (hi : InWordActivityOrthogonalComplement (f i)) :
    spectralTensor f (0 : State A n) = 0 := by
  have hfi := (inWordActivityOrthogonalComplement_iff_zero_and_sum (f i)).mp hi
  unfold spectralTensor
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa using hfi.1

/-- The pure-tensor form of the `k ≥ n` branch of the paper's MDS vanishing
lemma. `x` and `y` mark the unrestricted input and output word positions. -/
theorem linear_differenceDistributionMatrix_tensor_pairing_zero_of_low_activity
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) (hweight : activityWeight x + activityWeight y ≤ n)
    (f g : Fin n → A → ℝ)
    (hf : ∀ i, x i = false → f i = wordZeroIndicator (A := A))
    (hg : ∀ i, y i = false → g i = wordZeroIndicator (A := A))
    (horth : (∃ i, InWordActivityOrthogonalComplement (f i)) ∨
      (∃ i, InWordActivityOrthogonalComplement (g i))) :
    spectralTensor g ⬝ᵥ deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a) *ᵥ spectralTensor f = 0 := by
  apply linear_differenceDistributionMatrix_pairing_zero_of_low_activity_support
    L hMDS x y hweight
  · exact spectralTensor_zero_outside_activityBox x f hf
  · exact spectralTensor_zero_outside_activityBox y g hg
  · rcases horth with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl (spectralTensor_zero_of_orthogonal_factor f i hi)
    · exact Or.inr (spectralTensor_zero_of_orthogonal_factor g i hi)

omit [Fintype A] in
/-- The number of nonzero graph coordinates is the MDS branch weight. -/
theorem mdsGraphCoordinate_active_count
    (L : State A n ≃+ State A n) (a : State A n) :
    (Finset.univ.filter (fun j : Sum (Fin n) (Fin n) =>
      mdsGraphCoordinate L a j ≠ 0)).card =
      activeCoordinates a + activeCoordinates (L a) := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [activeCoordinates, mdsGraphCoordinate, Finset.card_filter]

omit [Fintype A] in
/-- An MDS graph codeword vanishing on at least `n` of its `2n` word
positions must be the zero codeword. This is the coordinate form of the
branch-number hypothesis used in the paper's vanishing proof. -/
theorem IsMDS.eq_zero_of_graph_zero_coordinates
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : n ≤ s.card)
    (a : State A n)
    (hzero : ∀ j ∈ s, mdsGraphCoordinate L a j = 0) : a = 0 := by
  by_contra hne
  let T : Finset (Sum (Fin n) (Fin n)) :=
    Finset.univ.filter (fun j => mdsGraphCoordinate L a j ≠ 0)
  have hsubset : T ⊆ sᶜ := by
    intro j hj
    have hjnonzero : mdsGraphCoordinate L a j ≠ 0 :=
      (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_compl]
    intro hjs
    exact hjnonzero (hzero j hjs)
  have hcard := Finset.card_le_card hsubset
  have htotal : T.card = activeCoordinates a + activeCoordinates (L a) :=
    mdsGraphCoordinate_active_count L a
  have huniv : (Finset.univ : Finset (Sum (Fin n) (Fin n))).card = 2 * n := by
    simp
    omega
  have hsle : s.card ≤ 2 * n := by
    calc
      s.card ≤ (Finset.univ : Finset (Sum (Fin n) (Fin n))).card :=
        Finset.card_le_card (Finset.subset_univ s)
      _ = 2 * n := huniv
  have hcompl : (sᶜ).card + s.card = 2 * n := by
    rw [Finset.card_compl]
    have hsize : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
      simp
      omega
    rw [hsize]
    omega
  have hbranch := hMDS a hne
  omega

/-- Restrict an MDS graph codeword to a selected set of input and output
word positions. -/
def mdsGraphProjection (L : State A n ≃+ State A n)
    (s : Finset (Sum (Fin n) (Fin n))) :
    State A n →+ (s → A) where
  toFun a j := mdsGraphCoordinate L a j
  map_zero' := by
    funext j
    cases j.1 <;> simp [mdsGraphCoordinate]
  map_add' a b := by
    funext j
    rcases j with ⟨j, hj⟩
    cases j <;> simp [mdsGraphCoordinate, map_add, Pi.add_apply]

omit [Fintype A] in
/-- A product of the paper's zero-indicator factors selects precisely
the codewords in the corresponding zero-coordinate fiber. -/
theorem graphZeroIndicator_product
    (L : State A n ≃+ State A n)
    (Z : Finset (Sum (Fin n) (Fin n))) (a : State A n) :
    (∏ j ∈ Z, wordZeroIndicator (A := A) (mdsGraphCoordinate L a j)) =
      if mdsGraphProjection L Z a = 0 then 1 else 0 := by
  classical
  by_cases hz : mdsGraphProjection L Z a = 0
  · rw [if_pos hz]
    apply Finset.prod_eq_one
    intro j hj
    have hcoord := congrFun hz ⟨j, hj⟩
    change mdsGraphCoordinate L a j = 0 at hcoord
    simp [wordZeroIndicator, hcoord]
  · rw [if_neg hz]
    have hnot : ¬ ∀ j ∈ Z, mdsGraphCoordinate L a j = 0 := by
      intro hh
      apply hz
      funext j
      exact hh j.1 j.2
    push_neg at hnot
    obtain ⟨j, hj, hne⟩ := hnot
    apply Finset.prod_eq_zero hj
    simp [wordZeroIndicator, hne]

/-- In a graph-code sum, zero-indicator factors restrict the sum to the
zero-coordinate fiber, leaving the other factors untouched. -/
theorem graphZeroIndicator_sum
    (L : State A n ≃+ State A n)
    (Z : Finset (Sum (Fin n) (Fin n))) (f : State A n → ℝ) :
    (∑ a : State A n,
      (∏ j ∈ Z, wordZeroIndicator (A := A)
        (mdsGraphCoordinate L a j)) * f a) =
      ∑ a ∈ (Finset.univ.filter (fun a : State A n =>
        mdsGraphProjection L Z a = 0)), f a := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [graphZeroIndicator_product]
  split <;> simp_all

/-- The paper's three kinds of graph-position factors give exactly a
zero-coordinate fiber sum of complementary factors, multiplied by the
normalization from the remaining constant factors. -/
theorem graphProductSum_eq_zeroFiberProduct
    (L : State A n ≃+ State A n)
    (Z I : Finset (Sum (Fin n) (Fin n))) (hdisj : Disjoint Z I)
    (w : Sum (Fin n) (Fin n) → A → ℝ) (v : I → A → ℝ) (c : ℝ)
    (hZ : ∀ j ∈ Z, w j = wordZeroIndicator (A := A))
    (hI : ∀ (j : Sum (Fin n) (Fin n)) (hj : j ∈ I),
      w j = v ⟨j, hj⟩)
    (hR : ∀ j ∉ Z ∪ I, w j = fun _ => c) :
    (∑ a : State A n,
      ∏ j : Sum (Fin n) (Fin n), w j (mdsGraphCoordinate L a j)) =
      c ^ ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card *
        ∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
          ∏ i : I, v i (mdsGraphCoordinate L a i.1) := by
  classical
  let R : Finset (Sum (Fin n) (Fin n)) := Finset.univ \ (Z ∪ I)
  have hsplit (a : State A n) :
      (∏ j : Sum (Fin n) (Fin n), w j (mdsGraphCoordinate L a j)) =
        c ^ R.card *
          ((∏ j ∈ Z, wordZeroIndicator (A := A)
            (mdsGraphCoordinate L a j)) *
            ∏ i : I, v i (mdsGraphCoordinate L a i.1)) := by
    have hprodR :
        (∏ j ∈ R, w j (mdsGraphCoordinate L a j)) = c ^ R.card := by
      calc
        (∏ j ∈ R, w j (mdsGraphCoordinate L a j)) = ∏ j ∈ R, c := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [hR j (Finset.mem_sdiff.mp hj).2]
        _ = c ^ R.card := by simp
    have hprodZ :
        (∏ j ∈ Z, w j (mdsGraphCoordinate L a j)) =
          ∏ j ∈ Z, wordZeroIndicator (A := A)
            (mdsGraphCoordinate L a j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hZ j hj]
    have hprodI :
        (∏ j ∈ I, w j (mdsGraphCoordinate L a j)) =
          ∏ i : I, v i (mdsGraphCoordinate L a i.1) := by
      calc
        (∏ j ∈ I, w j (mdsGraphCoordinate L a j)) =
            ∏ i : I, w i.1 (mdsGraphCoordinate L a i.1) :=
          (Finset.prod_coe_sort I
            (fun j => w j (mdsGraphCoordinate L a j))).symm
        _ = ∏ i : I, v i (mdsGraphCoordinate L a i.1) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hI i.1 i.2]
    calc
      (∏ j : Sum (Fin n) (Fin n), w j (mdsGraphCoordinate L a j)) =
          (∏ j ∈ R, w j (mdsGraphCoordinate L a j)) *
            ∏ j ∈ Z ∪ I, w j (mdsGraphCoordinate L a j) := by
        simpa [R] using
          (Finset.prod_sdiff (s₁ := Z ∪ I) (s₂ := Finset.univ)
            (f := fun j => w j (mdsGraphCoordinate L a j))
            (Finset.subset_univ _)).symm
      _ = c ^ R.card *
          ((∏ j ∈ Z, wordZeroIndicator (A := A)
            (mdsGraphCoordinate L a j)) *
            ∏ i : I, v i (mdsGraphCoordinate L a i.1)) := by
        rw [Finset.prod_union hdisj, hprodR, hprodZ, hprodI]
  simp_rw [hsplit]
  change (∑ a : State A n,
    c ^ R.card *
      ((∏ j ∈ Z, wordZeroIndicator (A := A)
        (mdsGraphCoordinate L a j)) *
        ∏ i : I, v i (mdsGraphCoordinate L a i.1))) = _
  rw [← Finset.mul_sum]
  congr 1
  exact graphZeroIndicator_sum L Z
    (fun a => ∏ i : I, v i (mdsGraphCoordinate L a i.1))

/-- A coordinate of `B_{l₁}ᵀ D_L B_{l₂}` in the paper's zero-fiber
form. The premises identify the zero-indicator and constant positions;
choosing `I` as the complementary-position set gives the paper's case. -/
theorem spectralBasisMatrix_linear_innerProduct_eq_zeroFiberProduct
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (Z I : Finset (Sum (Fin n) (Fin n))) (hdisj : Disjoint Z I)
    (hZ : ∀ j ∈ Z, spectralBasisGraphFactor l₁ l₂ c d j =
      wordZeroIndicator (A := A))
    (hR : ∀ j ∉ Z ∪ I, spectralBasisGraphFactor l₁ l₂ c d j =
      fun _ => (Real.sqrt (Fintype.card A : ℝ))⁻¹) :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) =
      ((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
        ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card *
        ∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
          ∏ i : I, spectralBasisGraphFactor l₁ l₂ c d i.1
            (mdsGraphCoordinate L a i.1) := by
  rw [spectralBasisMatrix_linear_innerProduct_eq_graphProductSum]
  exact graphProductSum_eq_zeroFiberProduct L Z I hdisj
    (spectralBasisGraphFactor l₁ l₂ c d)
    (fun i => spectralBasisGraphFactor l₁ l₂ c d i.1)
    ((Real.sqrt (Fintype.card A : ℝ))⁻¹) hZ
    (by intro j hj; rfl) hR

/-- The actual `B_{l₁}ᵀ D_L B_{l₂}` coordinate has the paper's
zero-fiber/product form with its zero and complementary positions
determined canonically by the two basis columns. -/
theorem spectralBasisMatrix_linear_innerProduct_eq_canonicalZeroFiberProduct
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
    let I := spectralBasisGraphComplementPositions l₁ l₂ c d
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) =
      ((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
        ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card *
        ∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
          ∏ i : I, spectralBasisGraphFactor l₁ l₂ c d i.1
            (mdsGraphCoordinate L a i.1) := by
  dsimp only
  exact spectralBasisMatrix_linear_innerProduct_eq_zeroFiberProduct
    L l₁ l₂ c d _ _
    (spectralBasisGraphZeroPositions_disjoint_complementPositions l₁ l₂ c d)
    (by intro j hj
        exact spectralBasisGraphFactor_eq_zero_of_mem_zeroPositions
          l₁ l₂ c d j hj)
    (by intro j hj
        exact spectralBasisGraphFactor_eq_uniform_of_not_mem_positions
          l₁ l₂ c d j hj)

omit [Fintype A] in
/-- Projection of an MDS graph code onto at least `n` word positions is
injective. -/
theorem IsMDS.graphProjection_injective
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : n ≤ s.card) :
    Function.Injective (mdsGraphProjection L s) := by
  intro a b hab
  have hmapzero : mdsGraphProjection L s (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hzero : ∀ j ∈ s, mdsGraphCoordinate L (a - b) j = 0 := by
    intro j hj
    exact congrFun hmapzero ⟨j, hj⟩
  exact sub_eq_zero.mp
    (hMDS.eq_zero_of_graph_zero_coordinates L s hs (a - b) hzero)

omit [Fintype A] in
/-- Within a fiber where the graph coordinates in `Z` are fixed to
zero, the coordinates in `T` determine the codeword whenever `Z ∪ T`
contains at least `n` positions. This is the injective free-coordinate
parameterization used by the paper's Frobenius count. -/
theorem IsMDS.graphProjection_injective_on_zero_fiber
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z T : Finset (Sum (Fin n) (Fin n)))
    (hcard : n ≤ (Z ∪ T).card)
    (a b : State A n)
    (ha : mdsGraphProjection L Z a = 0)
    (hb : mdsGraphProjection L Z b = 0)
    (hT : mdsGraphProjection L T a = mdsGraphProjection L T b) :
    a = b := by
  apply hMDS.graphProjection_injective L (Z ∪ T) hcard
  funext j
  rcases Finset.mem_union.mp j.2 with hZ | hT'
  · have ha' := congrFun ha ⟨j.1, hZ⟩
    have hb' := congrFun hb ⟨j.1, hZ⟩
    change mdsGraphCoordinate L a j.1 = 0 at ha'
    change mdsGraphCoordinate L b j.1 = 0 at hb'
    change mdsGraphCoordinate L a j.1 =
      mdsGraphCoordinate L b j.1
    rw [ha', hb']
  · have hT' := congrFun hT ⟨j.1, hT'⟩
    exact hT'

/-- The paper's `2^d(q-1)^d` MDS graph-code count. In the zero fiber
for `Z`, choose `T` among the complementary coordinates `I` so that
`Z ∪ T` determines a graph codeword. The factors outside `T` have
absolute value at most one, and projection to `T` is injective on the
fiber. This is the aggregate bound underlying the spectral Frobenius
estimate; the later matrix estimate must also count the choices of
`Z`, `I`, and the activity factors. -/
theorem IsMDS.graphZeroFiber_complementKernel_abs_sum_le
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z I T : Finset (Sum (Fin n) (Fin n)))
    (hTI : T ⊆ I) (hcard : n ≤ (Z ∪ T).card) :
    (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
        mdsGraphProjection L Z a = 0)),
      ∑ b ∈ (Finset.univ.filter (fun b : State A n =>
        mdsGraphProjection L Z b = 0)),
        ∏ j ∈ I,
          |wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|) ≤
      2 ^ T.card * ((Fintype.card A : ℝ) - 1) ^ T.card := by
  classical
  let C : Finset (State A n) := Finset.univ.filter
    (fun a => mdsGraphProjection L Z a = 0)
  let p : State A n → (T → A) := fun a => mdsGraphProjection L T a
  have hp : ∀ a ∈ C, ∀ b ∈ C, p a = p b → a = b := by
    intro a ha b hb hab
    exact hMDS.graphProjection_injective_on_zero_fiber L Z T hcard a b
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hfg : ∀ a ∈ C, ∀ b ∈ C,
      (∏ j ∈ I,
        |wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|) ≤
      ∏ j : T,
        |wordComplementBasisKernel (A := A) (p a j) (p b j)| := by
    intro a ha b hb
    have h := product_subset_le_of_nonneg_of_le_one T I hTI
      (fun j => |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|)
      (by intro j hj; exact abs_nonneg _)
      (by
        intro j hj
        exact wordComplementBasisKernel_abs_le_one (A := A)
          (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j))
    change (∏ j ∈ I,
      |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|) ≤
      ∏ j : T,
        |wordComplementBasisKernel (A := A)
          (mdsGraphCoordinate L a j.1) (mdsGraphCoordinate L b j.1)|
    rw [Finset.prod_coe_sort (s := T)
      (f := fun j => |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|)]
    exact h
  have hg : ∀ u v : T → A,
      0 ≤ ∏ j : T,
        |wordComplementBasisKernel (A := A) (u j) (v j)| := by
    intro u v
    exact Finset.prod_nonneg (fun j hj => abs_nonneg _)
  have hbound := sum_pairs_le_full_of_injective C p hp
    (fun a b => ∏ j ∈ I,
      |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|)
    (fun u v => ∏ j : T,
      |wordComplementBasisKernel (A := A) (u j) (v j)|)
    hfg hg
  exact hbound.trans (by simpa using
    (wordComplementBasisKernel_abs_free_pairs_le_finite
      (A := A) (J := T)))

/-- The same MDS codeword count in the paper's `k` notation: if
`k = |Z|`, then the zero-coordinate fiber has `n-k` free word
coordinates, and the complementary-kernel double sum is bounded by
`2^(n-k)(q-1)^(n-k)`. The disjointness premise records that zero
indicators and complementary factors occupy different word positions. -/
theorem IsMDS.graphZeroFiber_complementKernel_abs_sum_le_of_card
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z I : Finset (Sum (Fin n) (Fin n)))
    (hdisj : Disjoint Z I) (hZ : Z.card ≤ n)
    (hcover : n ≤ Z.card + I.card) :
    (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
        mdsGraphProjection L Z a = 0)),
      ∑ b ∈ (Finset.univ.filter (fun b : State A n =>
        mdsGraphProjection L Z b = 0)),
        ∏ j ∈ I,
          |wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|) ≤
      2 ^ (n - Z.card) *
        ((Fintype.card A : ℝ) - 1) ^ (n - Z.card) := by
  have hsize : n - Z.card ≤ I.card := by omega
  obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq hsize
  have hdisjZT : Disjoint Z T := hdisj.mono_right hTI
  have hUnion : (Z ∪ T).card = n := by
    rw [Finset.card_union_of_disjoint hdisjZT, hTcard]
    omega
  simpa [hTcard] using
    hMDS.graphZeroFiber_complementKernel_abs_sum_le L Z I T hTI
      (by omega : n ≤ (Z ∪ T).card)

/-- The paper's fixed-position squared-coordinate estimate before
counting which positions carry zero indicators, complementary vectors,
and normalized all-indicators. The left side sums the squared graph-code
pairings over every choice of complementary one-word basis vectors.
The bound is `2^(n-k)(q-1)^(n-k)` for `k = |Z|`. -/
theorem IsMDS.graphZeroFiber_complementBasis_sum_squares_le
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (Z I : Finset (Sum (Fin n) (Fin n)))
    (hdisj : Disjoint Z I) (hZ : Z.card ≤ n)
    (hcover : n ≤ Z.card + I.card) :
    (∑ j : (I → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
          mdsGraphProjection L Z a = 0)),
        ∏ i : I, wordComplementBasisVector (A := A) (j i)
          (mdsGraphCoordinate L a i.1)) ^ 2) ≤
      2 ^ (n - Z.card) *
        ((Fintype.card A : ℝ) - 1) ^ (n - Z.card) := by
  classical
  let C : Finset (State A n) := Finset.univ.filter
    (fun a => mdsGraphProjection L Z a = 0)
  have hexact := wordComplementBasisKernel_sum_squares_finite
    (A := A) (J := I) C (fun a i => mdsGraphCoordinate L a i.1)
  have hpoint (a b : State A n) :
      (∏ i : I, wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a i.1) (mdsGraphCoordinate L b i.1)) ≤
      ∏ i : I, |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a i.1) (mdsGraphCoordinate L b i.1)| := by
    rw [← Finset.abs_prod]
    exact le_abs_self _
  have hprod (a b : State A n) :
      (∏ i : I, |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a i.1) (mdsGraphCoordinate L b i.1)|) =
      ∏ j ∈ I, |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)| :=
    Finset.prod_coe_sort (s := I) (f := fun j =>
      |wordComplementBasisKernel (A := A)
        (mdsGraphCoordinate L a j) (mdsGraphCoordinate L b j)|)
  calc
    (∑ j : (I → Fin (Module.finrank ℝ
      (wordActivityHilbertSubspace (A := A))ᗮ)),
      (∑ a ∈ C,
        ∏ i : I, wordComplementBasisVector (A := A) (j i)
          (mdsGraphCoordinate L a i.1)) ^ 2) =
        ∑ a ∈ C, ∑ b ∈ C,
          ∏ i : I, wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a i.1)
            (mdsGraphCoordinate L b i.1) := hexact
    _ ≤ ∑ a ∈ C, ∑ b ∈ C,
          ∏ i : I, |wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a i.1)
            (mdsGraphCoordinate L b i.1)| := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hpoint a b
    _ = ∑ a ∈ C, ∑ b ∈ C,
          ∏ j ∈ I, |wordComplementBasisKernel (A := A)
            (mdsGraphCoordinate L a j)
            (mdsGraphCoordinate L b j)| := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hprod a b
    _ ≤ _ := hMDS.graphZeroFiber_complementKernel_abs_sum_le_of_card
      L Z I hdisj hZ hcover

set_option maxHeartbeats 800000 in
/-- For fixed complementary and activity positions, summing the squared coordinates of `B_{l₁}ᵀ D_L B_{l₂}` over the two columns' complementary-basis choices is exactly one sum over all complementary graph-position choices. This is the paper's Frobenius summation step before applying the MDS bound. -/
theorem spectralBasisMatrix_fixedActivity_sum_squares_eq
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
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
      α ^ 2 *
        ∑ j : I → Fin (Module.finrank ℝ
          (wordActivityHilbertSubspace (A := A))ᗮ),
          (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
            mdsGraphProjection L Z a = 0)),
            ∏ i : I, wordComplementBasisVector (A := A) (j i)
              (mdsGraphCoordinate L a i.1)) ^ 2 := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  let C : Finset (State A n) := Finset.univ.filter
    (fun a => mdsGraphProjection L Z a = 0)
  let α : ℝ := ((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
    ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card
  let E := spectralBasisGraphComplementChoicesEquiv l₁ l₂ c d
  have hentry
      (g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
      (f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
      (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁ c f)
            (spectralBasisIndex_withComplementChoices l₂ d g)) =
        α * (∑ a ∈ C,
          ∏ i : I, wordComplementBasisVector (A := A) (E (g, f) i)
            (mdsGraphCoordinate L a i.1)) := by
    have hraw :=
      spectralBasisMatrix_linear_innerProduct_eq_canonicalZeroFiberProduct
        L l₁ l₂
          (spectralBasisIndex_withComplementChoices l₁ c f)
          (spectralBasisIndex_withComplementChoices l₂ d g)
    dsimp only at hraw
    rw [spectralBasisGraphZeroPositions_withChoices,
      spectralBasisGraphComplementPositions_withChoices] at hraw
    rw [hraw]
    change α * (∑ a ∈ C,
      ∏ i : I, spectralBasisGraphFactor l₁ l₂
        (spectralBasisIndex_withComplementChoices l₁ c f)
        (spectralBasisIndex_withComplementChoices l₂ d g) i.1
          (mdsGraphCoordinate L a i.1)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro i hi
    rw [spectralBasisGraphFactor_withChoices_of_mem_complement l₁ l₂ c d f g i]
  dsimp only
  calc
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
      ∑ g, ∑ f,
        α ^ 2 *
          (∑ a ∈ C,
            ∏ i : I, wordComplementBasisVector (A := A) (E (g, f) i)
              (mdsGraphCoordinate L a i.1)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        apply Finset.sum_congr rfl
        intro f hf
        rw [hentry g f, mul_pow]
    _ = α ^ 2 *
      ∑ g, ∑ f,
        (∑ a ∈ C,
          ∏ i : I, wordComplementBasisVector (A := A) (E (g, f) i)
            (mdsGraphCoordinate L a i.1)) ^ 2 := by
        simp_rw [Finset.mul_sum]
    _ = α ^ 2 *
      ∑ j : I → Fin (Module.finrank ℝ
          (wordActivityHilbertSubspace (A := A))ᗮ),
        (∑ a ∈ C,
          ∏ i : I, wordComplementBasisVector (A := A) (j i)
            (mdsGraphCoordinate L a i.1)) ^ 2 := by
        congr 1
        exact spectralBasisGraphComplementChoices_sum l₁ l₂ c d
          (fun j => (∑ a ∈ C,
            ∏ i : I, wordComplementBasisVector (A := A) (j i)
              (mdsGraphCoordinate L a i.1)) ^ 2)

/-- For fixed complementary and activity positions, the full sum over the two columns' complementary-basis choices satisfies the paper's `2^(n-k)(q-1)^(n-k)` MDS estimate with the normalized all-indicator factor. -/
theorem IsMDS.spectralBasisMatrix_fixedActivity_sum_squares_le
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hZ : (spectralBasisGraphZeroPositions l₁ l₂ c d).card ≤ n)
    (hcover : n ≤
      (spectralBasisGraphZeroPositions l₁ l₂ c d).card + l₁ + l₂) :
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
            (spectralBasisIndex_withComplementChoices l₂ d g)) ^ 2)) ≤
      α ^ 2 *
        (2 ^ (n - Z.card) *
          ((Fintype.card A : ℝ) - 1) ^ (n - Z.card)) := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  let α : ℝ := ((Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
    ((Finset.univ : Finset (Sum (Fin n) (Fin n))) \ (Z ∪ I)).card
  have hdisj : Disjoint Z I :=
    spectralBasisGraphZeroPositions_disjoint_complementPositions l₁ l₂ c d
  have hcover' : n ≤ Z.card + I.card := by
    have hcover'' : n ≤ Z.card + l₁ + l₂ := hcover
    rw [spectralBasisGraphComplementPositions_card]
    omega
  have hM := hMDS.graphZeroFiber_complementBasis_sum_squares_le
    L Z I hdisj hZ hcover'
  have hEq := spectralBasisMatrix_fixedActivity_sum_squares_eq L l₁ l₂ c d
  dsimp only at hEq
  dsimp only
  rw [hEq]
  exact mul_le_mul_of_nonneg_left hM (sq_nonneg α)

/-- The fixed-position squared-coordinate sum in the paper's normalization: `k` zero-indicator positions and `l₁+l₂` complementary positions leave a factor `q^(-(2n-k-l₁-l₂))`. -/
theorem IsMDS.spectralBasisMatrix_fixedActivity_sum_squares_le_paperNormalization
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hZ : (spectralBasisGraphZeroPositions l₁ l₂ c d).card ≤ n)
    (hcover : n ≤
      (spectralBasisGraphZeroPositions l₁ l₂ c d).card + l₁ + l₂) :
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
            (spectralBasisIndex_withComplementChoices l₂ d g)) ^ 2)) ≤
      ((Fintype.card A : ℝ)⁻¹) ^
        (2 * n - Z.card - (l₁ + l₂)) *
        (2 ^ (n - Z.card) *
          ((Fintype.card A : ℝ) - 1) ^ (n - Z.card)) := by
  have hb := hMDS.spectralBasisMatrix_fixedActivity_sum_squares_le
    L l₁ l₂ c d hZ hcover
  have hc := spectralBasisGraphUniformPositions_card l₁ l₂ c d
  dsimp only at hb hc ⊢
  rw [hc] at hb
  rw [normalizedAllIndicatorFactor_sq] at hb
  exact hb

/-- Projection of an MDS graph code onto exactly `n` word positions is
bijective, the rank statement underlying the paper's uniform-fiber
argument. -/
theorem IsMDS.graphProjection_bijective
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card = n) :
    Function.Bijective (mdsGraphProjection L s) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card
    (mdsGraphProjection L s)).2
  constructor
  · exact hMDS.graphProjection_injective L s (by omega)
  · simp [State, hs]

/-- Every selection of at most `n` input and output word positions takes
every possible assignment on an MDS graph codeword. -/
theorem IsMDS.graphProjection_surjective
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card ≤ n) :
    Function.Surjective (mdsGraphProjection L s) := by
  classical
  have hcardUniv : n ≤
      (Finset.univ : Finset (Sum (Fin n) (Fin n))).card := by
    simp
  obtain ⟨t, hst, _htu, htcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs hcardUniv
  have hbij := hMDS.graphProjection_bijective L t htcard
  intro target
  let targetT : t → A := fun j =>
    if h : j.1 ∈ s then target ⟨j.1, h⟩ else 0
  obtain ⟨a, ha⟩ := hbij.2 targetT
  refine ⟨a, ?_⟩
  funext j
  have hj := congrFun ha ⟨j.1, hst j.2⟩
  simpa [mdsGraphProjection, targetT, j.2] using hj

/-- Every assignment to at most `n` selected graph coordinates occurs
equally often. This is the uniform-fiber statement used in the paper's
`k + l ≤ n` vanishing case. -/
theorem IsMDS.graphProjection_fiber_card_eq
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card ≤ n)
    (b c : s → A) :
    (Finset.univ.filter (fun a : State A n => mdsGraphProjection L s a = b)).card =
      (Finset.univ.filter (fun a : State A n => mdsGraphProjection L s a = c)).card := by
  classical
  have hsurj := hMDS.graphProjection_surjective L s hs
  exact AddMonoidHom.card_fiber_eq_of_mem_range (mdsGraphProjection L s)
    (Set.mem_range.mpr (hsurj b)) (Set.mem_range.mpr (hsurj c))

/-- Summing a function of at most `n` MDS graph coordinates gives the
uniform-fiber multiplicity times the sum over all assignments. -/
theorem IsMDS.sum_graphProjection_eq_fiber_mul_sum
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card ≤ n)
    (F : (s → A) → ℝ) :
    (∑ a : State A n, F (mdsGraphProjection L s a)) =
      ((Finset.univ.filter (fun a : State A n =>
        mdsGraphProjection L s a = 0)).card : ℝ) *
        ∑ b : s → A, F b := by
  classical
  let P := mdsGraphProjection L s
  calc
    (∑ a : State A n, F (P a)) =
        ∑ b : s → A,
          ∑ a ∈ (Finset.univ : Finset (State A n)) with P a = b, F b :=
      (Finset.sum_fiberwise' Finset.univ P F).symm
    _ = ∑ b : s → A,
          ((Finset.univ.filter (fun a : State A n => P a = b)).card : ℝ) *
            F b := by
      congr 1
      funext b
      simp [nsmul_eq_mul]
    _ = ((Finset.univ.filter (fun a : State A n => P a = 0)).card : ℝ) *
          ∑ b : s → A, F b := by
      have hcard (b : s → A) :
          (Finset.univ.filter (fun a : State A n => P a = b)).card =
            (Finset.univ.filter (fun a : State A n => P a = 0)).card :=
        hMDS.graphProjection_fiber_card_eq L s hs b 0
      simp_rw [hcard]
      rw [Finset.mul_sum]

/-- If one selected graph-coordinate factor has zero total sum, the
weighted sum over all MDS graph codewords vanishes whenever at most `n`
coordinates are selected. This is the cancellation mechanism in the
paper's `k + l ≤ n` case. -/
theorem IsMDS.sum_graphProjection_product_zero
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card ≤ n)
    (w : s → A → ℝ) (p : s)
    (hp : (∑ a : A, w p a) = 0) :
    (∑ a : State A n,
      ∏ j : s, w j (mdsGraphProjection L s a j)) = 0 := by
  rw [hMDS.sum_graphProjection_eq_fiber_mul_sum L s hs
    (fun b : s → A => ∏ j : s, w j (b j))]
  have hsum : (∑ b : s → A, ∏ j : s, w j (b j)) = 0 := by
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    exact hp
  rw [hsum, mul_zero]

/-- The `k + l ≤ n` cancellation in the paper's form: all nonconstant
factors are supported on at most `n` graph positions, and at least one of
those factors has zero total sum. -/
theorem IsMDS.graph_tensor_product_sum_zero
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (s : Finset (Sum (Fin n) (Fin n))) (hs : s.card ≤ n)
    (w : Sum (Fin n) (Fin n) → A → ℝ)
    (houtside : ∀ j ∉ s, w j = wordAllIndicator (A := A))
    (p : Sum (Fin n) (Fin n)) (hp : p ∈ s)
    (hpmean : (∑ a : A, w p a) = 0) :
    (∑ a : State A n,
      ∏ j : Sum (Fin n) (Fin n),
        w j (mdsGraphCoordinate L a j)) = 0 := by
  have hrestrict (a : State A n) :
      (∏ j : Sum (Fin n) (Fin n),
        w j (mdsGraphCoordinate L a j)) =
      ∏ j : s, w j.1 (mdsGraphProjection L s a j) := by
    calc
      (∏ j : Sum (Fin n) (Fin n),
        w j (mdsGraphCoordinate L a j)) =
          ∏ j ∈ s, w j (mdsGraphCoordinate L a j) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ s)
        intro j _ hj
        simp [houtside j hj, wordAllIndicator]
      _ = ∏ j : s, w j.1 (mdsGraphProjection L s a j) := by
        exact (Finset.prod_coe_sort s
          (fun j => w j (mdsGraphCoordinate L a j))).symm
  simp_rw [hrestrict]
  exact hMDS.sum_graphProjection_product_zero L s hs
    (fun j => w j.1) ⟨p, hp⟩ hpmean

/-- The activity pattern whose input word is unrestricted exactly when its
graph position is not among the forced-zero positions. -/
def graphInputActivityPattern
    (Z : Finset (Sum (Fin n) (Fin n))) (i : Fin n) : Bool :=
  decide (Sum.inl i ∉ Z)

/-- The corresponding output activity pattern. -/
def graphOutputActivityPattern
    (Z : Finset (Sum (Fin n) (Fin n))) (i : Fin n) : Bool :=
  decide (Sum.inr i ∉ Z)

/-- The total number of unrestricted positions in these two patterns is
the complement of the set of forced-zero graph positions. -/
theorem graphActivityPatterns_weight_eq_compl_card
    (Z : Finset (Sum (Fin n) (Fin n))) :
    activityWeight (graphInputActivityPattern (n := n) Z) +
      activityWeight (graphOutputActivityPattern (n := n) Z) = (Zᶜ).card := by
  classical
  have hcomp : Zᶜ = Finset.univ.filter (fun j => j ∉ Z) := by
    ext j
    simp
  rw [hcomp]
  simp only [activityWeight, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [graphInputActivityPattern, graphOutputActivityPattern]

/-- For `l₁+l₂ > 0`, an actual coordinate of `B_{l₁}ᵀ D_L B_{l₂}` vanishes when at least `n` graph factors are zero indicators. This is the paper's high-`k` cutoff for the Frobenius sum. -/
theorem spectralBasisMatrix_linear_innerProduct_zero_of_manyZeros
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hZ : n ≤ (spectralBasisGraphZeroPositions l₁ l₂ c d).card) :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) = 0 := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  let f := spectralBasisWordFactor l₂ d
  let g := spectralBasisWordFactor l₁ c
  let x := graphInputActivityPattern (n := n) Z
  let y := graphOutputActivityPattern (n := n) Z
  have hweight : activityWeight x + activityWeight y ≤ n := by
    have hcount := graphActivityPatterns_weight_eq_compl_card (n := n) Z
    have hZle : Z.card ≤ 2 * n := by
      calc
        Z.card ≤ (Finset.univ : Finset (Sum (Fin n) (Fin n))).card :=
          Finset.card_le_card (Finset.subset_univ Z)
        _ = 2 * n := by simp; omega
    have hsize : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
      simp
      omega
    rw [Finset.card_compl, hsize] at hcount
    have hcount' : activityWeight x + activityWeight y = 2 * n - Z.card := by
      simpa only [x, y] using hcount
    change n ≤ Z.card at hZ
    omega
  have hfx : ∀ i, x i = false → f i = wordZeroIndicator (A := A) := by
    intro i hi
    have hmem : Sum.inl i ∈ Z := by
      simpa [x, graphInputActivityPattern] using hi
    exact spectralBasisGraphFactor_eq_zero_of_mem_zeroPositions l₁ l₂ c d _ hmem
  have hgy : ∀ i, y i = false → g i = wordZeroIndicator (A := A) := by
    intro i hi
    have hmem : Sum.inr i ∈ Z := by
      simpa [y, graphOutputActivityPattern] using hi
    exact spectralBasisGraphFactor_eq_zero_of_mem_zeroPositions l₁ l₂ c d _ hmem
  have hI : I.Nonempty := Finset.card_pos.mp (by
    rw [spectralBasisGraphComplementPositions_card]
    exact hpos)
  obtain ⟨j, hj⟩ := hI
  obtain ⟨k, hk⟩ :=
    spectralBasisGraphFactor_eq_complement_of_mem_complementPositions
      l₁ l₂ c d j hj
  have hfactor : (∃ i, InWordActivityOrthogonalComplement (f i)) ∨
      (∃ i, InWordActivityOrthogonalComplement (g i)) := by
    cases j with
    | inl i =>
        exact Or.inl ⟨i, by
          change f i = wordComplementBasisVector (A := A) k at hk
          rw [hk]
          exact wordComplementBasisVector_orthogonal (A := A) k⟩
    | inr i =>
        exact Or.inr ⟨i, by
          change g i = wordComplementBasisVector (A := A) k at hk
          rw [hk]
          exact wordComplementBasisVector_orthogonal (A := A) k⟩
  have hvanish := linear_differenceDistributionMatrix_tensor_pairing_zero_of_low_activity
    L hMDS x y hweight f g hfx hgy hfactor
  have hentry :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) =
        spectralTensor g ⬝ᵥ deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *ᵥ spectralTensor f := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
    rfl
  rw [hentry]
  exact hvanish

/-- For `l₁+l₂ > 0`, an actual coordinate of `B_{l₁}ᵀ D_L B_{l₂}` vanishes when the zero and complementary factors together occupy at most `n` graph positions. This is the paper's low-`k+l` cutoff for the Frobenius sum. -/
theorem spectralBasisMatrix_linear_innerProduct_zero_of_fewConstraints
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂)
    (hK : (spectralBasisGraphZeroPositions l₁ l₂ c d).card + l₁ + l₂ ≤ n) :
    (((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂) c d) = 0 := by
  classical
  let Z := spectralBasisGraphZeroPositions l₁ l₂ c d
  let I := spectralBasisGraphComplementPositions l₁ l₂ c d
  let s := Z ∪ I
  let w : Sum (Fin n) (Fin n) → A → ℝ := fun j =>
    if j ∈ s then spectralBasisGraphFactor l₁ l₂ c d j
    else wordAllIndicator (A := A)
  have hdisj : Disjoint Z I :=
    spectralBasisGraphZeroPositions_disjoint_complementPositions l₁ l₂ c d
  have hs : s.card ≤ n := by
    rw [Finset.card_union_of_disjoint hdisj]
    have hcardI := spectralBasisGraphComplementPositions_card l₁ l₂ c d
    change I.card = l₁ + l₂ at hcardI
    change Z.card + l₁ + l₂ ≤ n at hK
    omega
  have hI : I.Nonempty := Finset.card_pos.mp (by
    rw [spectralBasisGraphComplementPositions_card]
    exact hpos)
  obtain ⟨p, hpI⟩ := hI
  have hpS : p ∈ s := Finset.mem_union_right Z hpI
  have hpmean : (∑ a : A, w p a) = 0 := by
    obtain ⟨k, hk⟩ :=
      spectralBasisGraphFactor_eq_complement_of_mem_complementPositions
        l₁ l₂ c d p hpI
    have hw : w p = wordComplementBasisVector (A := A) k := by
      simp [w, hpS, hk]
    rw [hw]
    exact (inWordActivityOrthogonalComplement_iff_zero_and_sum _).mp
      (wordComplementBasisVector_orthogonal (A := A) k) |>.2
  have hsum : (∑ a : State A n,
      ∏ j : Sum (Fin n) (Fin n), w j (mdsGraphCoordinate L a j)) = 0 :=
    hMDS.graph_tensor_product_sum_zero L s hs w
      (by intro j hj; simp [w, hj]) p hpS hpmean
  have hZ : ∀ j ∈ Z, w j = wordZeroIndicator (A := A) := by
    intro j hj
    rw [show w j = spectralBasisGraphFactor l₁ l₂ c d j from by
      simp [w, s, hj]]
    exact spectralBasisGraphFactor_eq_zero_of_mem_zeroPositions l₁ l₂ c d j hj
  have hI' : ∀ (j : Sum (Fin n) (Fin n)) (hj : j ∈ I),
      w j = spectralBasisGraphFactor l₁ l₂ c d j := by
    intro j hj
    simp [w, s, hj]
  have hR : ∀ j ∉ Z ∪ I, w j = wordAllIndicator (A := A) := by
    intro j hj
    have hjs : j ∉ s := by simpa [s] using hj
    simp [w, hjs]
  have hfiber := graphProductSum_eq_zeroFiberProduct L Z I hdisj w
    (fun i => spectralBasisGraphFactor l₁ l₂ c d i.1) 1 hZ hI' hR
  simp only [one_pow, one_mul] at hfiber
  have hfiberzero :
      (∑ a ∈ (Finset.univ.filter (fun a : State A n =>
        mdsGraphProjection L Z a = 0)),
          ∏ i : I, spectralBasisGraphFactor l₁ l₂ c d i.1
            (mdsGraphCoordinate L a i.1)) = 0 := by
    rw [← hfiber]
    exact hsum
  have hentry := spectralBasisMatrix_linear_innerProduct_eq_canonicalZeroFiberProduct
    L l₁ l₂ c d
  dsimp only at hentry
  rw [hentry, hfiberzero, mul_zero]

/-- The squared Frobenius coordinate sum for `B_{l₁}ᵀ D_L B_{l₂}` with both columns' complementary-position sets fixed; activity bits and complementary basis choices vary. -/
noncomputable def spectralBasisMatrix_fixedComplementPositions_sum_squares
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) : ℝ :=
  ∑ p : (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool)),
    ∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁
              (spectralBasisIndex_withActivityChoices l₁ c p.2) f)
            (spectralBasisIndex_withComplementChoices l₂
              (spectralBasisIndex_withActivityChoices l₂ d p.1) g)) ^ 2)

/-- The paper's spectral Frobenius sum after fixing only the two complementary-position sets: the MDS estimate is summed over exactly the permitted zero-indicator counts, each with its binomial multiplicity. -/
theorem IsMDS.spectralBasisMatrix_fixedComplementPositions_sum_squares_le
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂ c d ≤
      ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
        (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
          (if k < n ∧ n < k + l₁ + l₂ then
            ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
              (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
          else 0) := by
  classical
  let P := (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool))
  let count : P → ℕ := fun p =>
    (spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c p.2)
      (spectralBasisIndex_withActivityChoices l₂ d p.1)).card
  let F : ℕ → ℝ := fun k =>
    if k < n ∧ n < k + l₁ + l₂ then
      ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
        (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
    else 0
  let entrySum : P → ℝ := fun p =>
    ∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁
              (spectralBasisIndex_withActivityChoices l₁ c p.2) f)
            (spectralBasisIndex_withComplementChoices l₂
              (spectralBasisIndex_withActivityChoices l₂ d p.1) g)) ^ 2)
  have hpoint (p : P) : entrySum p ≤ F (count p) := by
    let cp := spectralBasisIndex_withActivityChoices l₁ c p.2
    let dp := spectralBasisIndex_withActivityChoices l₂ d p.1
    by_cases hvalid : count p < n ∧ n < count p + l₁ + l₂
    · have hb := hMDS.spectralBasisMatrix_fixedActivity_sum_squares_le_paperNormalization
        L l₁ l₂ cp dp (by change count p ≤ n; omega) (by
          change n ≤ count p + l₁ + l₂
          omega)
      simpa only [F, if_pos hvalid, entrySum, count, cp, dp] using hb
    · have hbad : n ≤ count p ∨ count p + l₁ + l₂ ≤ n := by omega
      have hzero (g : {i : Fin n // i ∈ d.1.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
          (f : {i : Fin n // i ∈ c.1.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
          ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
            deterministicDifferenceDistributionMatrix
              (fun a : State A n => L a) *
            spectralBasisMatrix (A := A) (n := n) l₂)
              (spectralBasisIndex_withComplementChoices l₁ cp f)
              (spectralBasisIndex_withComplementChoices l₂ dp g))) = 0 := by
        rcases hbad with hhigh | hlow
        · apply spectralBasisMatrix_linear_innerProduct_zero_of_manyZeros
            L hMDS l₁ l₂ hpos
          rw [spectralBasisGraphZeroPositions_withChoices]
          exact hhigh
        · apply spectralBasisMatrix_linear_innerProduct_zero_of_fewConstraints
            L hMDS l₁ l₂ hpos
          rw [spectralBasisGraphZeroPositions_withChoices]
          exact hlow
      have hentry : entrySum p = 0 := by
        dsimp only [entrySum]
        apply Finset.sum_eq_zero
        intro g hg
        apply Finset.sum_eq_zero
        intro f hf
        rw [hzero g f]
        norm_num
      rw [hentry]
      simp [F, hvalid]
  calc
    spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂ c d = ∑ p : P, entrySum p := rfl
    _ ≤ ∑ p : P, F (count p) := Finset.sum_le_sum (by
      intro p hp
      exact hpoint p)
    _ = _ := spectralBasisGraphActivityChoices_sum_by_zeroCount l₁ l₂ c d F

/-- Reorder four independent finite choices into the activity-first order used in the paper's spectral Frobenius sum. -/
theorem sum_two_product_pairs_reorder
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    (∑ x : α × β, ∑ y : γ × δ, F x.1 x.2 y.1 y.2) =
      ∑ p : δ × β, ∑ g : γ, ∑ f : α, F f p.2 g p.1 := by
  let e : ((α × β) × (γ × δ)) ≃ ((δ × β) × (γ × α)) := {
    toFun := fun z => ((z.2.2, z.1.2), (z.2.1, z.1.1))
    invFun := fun z => ((z.2.2, z.1.2), (z.2.1, z.1.1))
    left_inv := by intro z; rcases z with ⟨⟨a,b⟩,⟨g,d⟩⟩; rfl
    right_inv := by intro z; rcases z with ⟨⟨d,b⟩,⟨g,a⟩⟩; rfl
  }
  calc
    (∑ x : α × β, ∑ y : γ × δ, F x.1 x.2 y.1 y.2) =
        ∑ z : ((α × β) × (γ × δ)), F z.1.1 z.1.2 z.2.1 z.2.2 := by
          exact (Fintype.sum_prod_type
            (fun z : ((α × β) × (γ × δ)) => F z.1.1 z.1.2 z.2.1 z.2.2)).symm
    _ = ∑ z : ((δ × β) × (γ × α)), F z.2.2 z.1.2 z.2.1 z.1.1 := by
      apply Fintype.sum_equiv e
      intro z
      rfl
    _ = ∑ p : δ × β, ∑ g : γ, ∑ f : α, F f p.2 g p.1 := by
      rw [Fintype.sum_prod_type
        (fun z : ((δ × β) × (γ × α)) => F z.2.2 z.1.2 z.2.1 z.1.1)]
      apply Finset.sum_congr rfl
      intro p hp
      exact Fintype.sum_prod_type (fun z : γ × α => F z.2 p.2 z.1 p.1)

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}

/-- Sum a function of two spectral basis columns over all basis-vector and activity choices at fixed complementary-position sets. -/
noncomputable def spectralBasisIndex_fixedPositionSet_sum
    (l₁ l₂ : ℕ)
    (F : SpectralBasisIndex (A := A) (n := n) l₁ →
      SpectralBasisIndex (A := A) (n := n) l₂ → ℝ)
    (I₁ : {I : Finset (Fin n) // I.card = l₁})
    (I₂ : {I : Finset (Fin n) // I.card = l₂}) : ℝ :=
  ∑ p : (({i : Fin n // i ∉ I₂.1} → Bool) ×
       ({i : Fin n // i ∉ I₁.1} → Bool)),
    ∑ g : {i : Fin n // i ∈ I₂.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ I₁.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
          F ⟨I₁, (f,p.2)⟩ ⟨I₂,(g,p.1)⟩

set_option maxHeartbeats 800000 in
/-- The sum over every pair of paper-style `B_l` columns is exactly the sum over both complementary-position sets and then the choices at those positions. -/
theorem spectralBasisIndex_pair_sum_by_positionSets
    (l₁ l₂ : ℕ)
    (F : SpectralBasisIndex (A := A) (n := n) l₁ →
      SpectralBasisIndex (A := A) (n := n) l₂ → ℝ) :
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂, F c d) =
      ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
          spectralBasisIndex_fixedPositionSet_sum l₁ l₂ F I₁ I₂ := by
  classical
  calc
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂, F c d) =
      ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ x₁ : ({i : Fin n // i ∈ I₁.1} →
            Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
            ({i : Fin n // i ∉ I₁.1} → Bool),
          ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
            ∑ x₂ : ({i : Fin n // i ∈ I₂.1} →
                Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
                ({i : Fin n // i ∉ I₂.1} → Bool),
              F ⟨I₁, x₁⟩ ⟨I₂, x₂⟩ := by
                rw [Fintype.sum_sigma]
                apply Finset.sum_congr rfl
                intro I₁ hI₁
                apply Finset.sum_congr rfl
                intro x₁ hx₁
                rw [Fintype.sum_sigma]
    _ = ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
          ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
            ∑ x₁ : ({i : Fin n // i ∈ I₁.1} →
                Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
                ({i : Fin n // i ∉ I₁.1} → Bool),
              ∑ x₂ : ({i : Fin n // i ∈ I₂.1} →
                  Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
                  ({i : Fin n // i ∉ I₂.1} → Bool),
                F ⟨I₁, x₁⟩ ⟨I₂, x₂⟩ := by
                  apply Finset.sum_congr rfl
                  intro I₁ hI₁
                  exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I₁ hI₁
      apply Finset.sum_congr rfl
      intro I₂ hI₂
      let G := fun (f : {i : Fin n // i ∈ I₁.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
          (z : {i : Fin n // i ∉ I₁.1} → Bool)
          (g : {i : Fin n // i ∈ I₂.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
          (w : {i : Fin n // i ∉ I₂.1} → Bool) =>
            F ⟨I₁,(f,z)⟩ ⟨I₂,(g,w)⟩
      let X₁ := ({i : Fin n // i ∈ I₁.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
          ({i : Fin n // i ∉ I₁.1} → Bool)
      let X₂ := ({i : Fin n // i ∈ I₂.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) ×
          ({i : Fin n // i ∉ I₂.1} → Bool)
      change (∑ x₁ : X₁, ∑ x₂ : X₂, G x₁.1 x₁.2 x₂.1 x₂.2) = _
      rw [sum_two_product_pairs_reorder G]
      rfl

/-- A reference spectral basis column at each complementary-position set, available when the one-word complement has positive dimension. Its initial activity and basis choices are overwritten in the full sum. -/
noncomputable def spectralBasisIndex_default
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)
    (l : ℕ) (I : {I : Finset (Fin n) // I.card = l}) :
    SpectralBasisIndex (A := A) (n := n) l :=
  ⟨I, (fun _ => ⟨0, hd⟩, fun _ => false)⟩

/-- The generic fixed-position column sum is definitionally the paper's fixed-position squared-entry sum for the reference columns. -/
theorem spectralBasisIndex_fixedPositionSet_sum_eq_fixedComplementPositions_sum_squares
    (L : State A n ≃+ State A n) (l₁ l₂ : ℕ)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)
    (I₁ : {I : Finset (Fin n) // I.card = l₁})
    (I₂ : {I : Finset (Fin n) // I.card = l₂}) :
    spectralBasisIndex_fixedPositionSet_sum l₁ l₂
      (fun c d => ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) I₁ I₂ =
      spectralBasisMatrix_fixedComplementPositions_sum_squares
        L l₁ l₂ (spectralBasisIndex_default hd l₁ I₁)
          (spectralBasisIndex_default hd l₂ I₂) := by
  rfl

/-- The paper's full squared Frobenius-entry estimate for `B_{l₁}ᵀ D_L B_{l₂}`. All spectral columns are counted once, with the paper's two `choose n lᵢ` factors and the exact valid range `k<n<k+l₁+l₂`. -/
theorem IsMDS.spectralBasisMatrix_fullFrobenius_sum_squares_le
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂,
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) ≤
      (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
        ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
          (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
            (if k < n ∧ n < k + l₁ + l₂ then
              ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
                (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
            else 0) := by
  classical
  let B : ℝ := ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
          (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
            (if k < n ∧ n < k + l₁ + l₂ then
              ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
                (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
            else 0)
  calc
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂,
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) =
      ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
          spectralBasisIndex_fixedPositionSet_sum l₁ l₂
            (fun c d => ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
              deterministicDifferenceDistributionMatrix
                (fun a : State A n => L a) *
              spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) I₁ I₂ :=
        spectralBasisIndex_pair_sum_by_positionSets l₁ l₂ _
    _ = ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
          spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂
            (spectralBasisIndex_default hd l₁ I₁)
            (spectralBasisIndex_default hd l₂ I₂) := by
        apply Finset.sum_congr rfl
        intro I₁ hI₁
        apply Finset.sum_congr rfl
        intro I₂ hI₂
        exact spectralBasisIndex_fixedPositionSet_sum_eq_fixedComplementPositions_sum_squares L l₁ l₂ hd I₁ I₂
    _ ≤ ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂}, B := by
        apply Finset.sum_le_sum
        intro I₁ hI₁
        apply Finset.sum_le_sum
        intro I₂ hI₂
        exact hMDS.spectralBasisMatrix_fixedComplementPositions_sum_squares_le
          L l₁ l₂ hpos (spectralBasisIndex_default hd l₁ I₁)
            (spectralBasisIndex_default hd l₂ I₂)
    _ = (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) * B := by
      simp [mul_assoc]

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- A zero word factor makes a pure tensor zero. -/
theorem spectralTensor_update_zero
    (f : Fin n → A → ℝ) (i : Fin n) :
    spectralTensor (Function.update f i 0) = 0 := by
  funext x
  change (∏ j : Fin n, (Function.update f i 0) j (x j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- Multilinearity of a pure tensor under scalar multiplication in one
word coordinate. -/
theorem spectralTensor_update_smul
    (f : Fin n → A → ℝ) (i : Fin n) (t : ℝ) (g : A → ℝ) :
    spectralTensor (Function.update f i (t • g)) =
      t • spectralTensor (Function.update f i g) := by
  classical
  funext x
  have hsplit (v : A → ℝ) :
      spectralTensor (Function.update f i v) x = v (x i) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j) := by
    unfold spectralTensor
    rw [(Finset.mul_prod_erase Finset.univ
      (fun j : Fin n => (Function.update f i v) j (x j))
      (Finset.mem_univ i)).symm]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Function.update_of_ne hji]
  rw [Pi.smul_apply, hsplit, hsplit]
  simp [smul_eq_mul, mul_assoc]

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- Multilinearity lets a tensor with each word factor in a chosen span
be reduced to tensors whose factors are actual generators. -/
theorem spectralTensor_mem_of_component_span
    (P : Submodule ℝ (State A n → ℝ))
    (u : Fin n → Set (A → ℝ))
    (hbase : ∀ g : Fin n → A → ℝ,
      (∀ i, g i ∈ u i) → spectralTensor g ∈ P)
    (f : Fin n → A → ℝ)
    (hf : ∀ i, f i ∈ Submodule.span ℝ (u i)) :
    spectralTensor f ∈ P := by
  classical
  have hprocess (s : Finset (Fin n)) :
      ∀ g : Fin n → A → ℝ,
        (∀ i, i ∉ s → g i ∈ u i) →
        (∀ i ∈ s, g i ∈ Submodule.span ℝ (u i)) →
        spectralTensor g ∈ P := by
    induction s using Finset.induction_on with
    | empty =>
        intro g hg _
        exact hbase g (by intro i; exact hg i (by simp))
    | @insert i s his ih =>
        intro g hg hspan
        have hmem (v : A → ℝ) (hv : v ∈ Submodule.span ℝ (u i)) :
            spectralTensor (Function.update g i v) ∈ P := by
          induction hv using Submodule.span_induction with
          | mem v hv =>
              apply ih (Function.update g i v)
              · intro j hj
                by_cases hji : j = i
                · subst j
                  simpa using hv
                · have hjold : j ∉ insert i s := by simp [hji, hj]
                  simpa [Function.update_of_ne hji] using hg j hjold
              · intro j hj
                have hji : j ≠ i := by
                  intro h
                  subst j
                  exact his hj
                simpa [Function.update_of_ne hji] using
                  hspan j (Finset.mem_insert_of_mem hj)
          | zero =>
              simp [spectralTensor_update_zero]
          | add v w _ _ hv hw =>
              have hsum := spectralTensor_update_add
                (Function.update g i (v + w)) i v w (by simp)
              rw [Function.update_idem, Function.update_idem] at hsum
              rw [hsum]
              exact P.add_mem hv hw
          | smul t v _ hv =>
              rw [spectralTensor_update_smul]
              exact P.smul_mem t hv
        have hi := hspan i (Finset.mem_insert_self i s)
        simpa using hmem (g i) hi
  exact hprocess Finset.univ f (by simp) (by simpa using hf)

/-- The columns of the paper's spectral basis matrix span exactly `W_l`.
This justifies using its Gram matrix for projected-operator estimates. -/
theorem spectralBasisColumnSubspace_eq_spectralWeightSubspace (l : ℕ) :
    spectralBasisColumnSubspace (A := A) (n := n) l =
      spectralWeightSubspace (A := A) (n := n) l := by
  classical
  apply le_antisymm
  · unfold spectralBasisColumnSubspace
    apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    exact spectralBasisMatrix_column_mem l c
  · unfold spectralWeightSubspace
    apply Submodule.span_le.mpr
    rintro v ⟨I, f, hcard, horth, hact, rfl⟩
    let P := spectralBasisColumnSubspace (A := A) (n := n) l
    let u (i : Fin n) : Set (A → ℝ) :=
      if i ∈ I then Set.range (wordComplementBasisVector (A := A))
      else Set.range (normalizedActivityWordVector (A := A))
    have hbase (g : Fin n → A → ℝ)
        (hg : ∀ i, g i ∈ u i) : spectralTensor g ∈ P := by
      have hcomp (i : {i : Fin n // i ∈ I}) :
          ∃ j, g i.1 = wordComplementBasisVector (A := A) j := by
        have hi := hg i.1
        simp only [u, if_pos i.2] at hi
        obtain ⟨j, hj⟩ := hi
        exact ⟨j, hj.symm⟩
      have hactivity (i : {i : Fin n // i ∉ I}) :
          ∃ z, g i.1 = normalizedActivityWordVector (A := A) z := by
        have hi := hg i.1
        simp only [u, if_neg i.2] at hi
        obtain ⟨z, hz⟩ := hi
        exact ⟨z, hz.symm⟩
      let j (i : {i : Fin n // i ∈ I}) := Classical.choose (hcomp i)
      let z (i : {i : Fin n // i ∉ I}) := Classical.choose (hactivity i)
      let c : SpectralBasisIndex (A := A) (n := n) l :=
        ⟨⟨I, hcard⟩, (j, z)⟩
      have heq : spectralTensor g =
          (fun a => spectralBasisMatrix (A := A) (n := n) l a c) := by
        change spectralTensor g = spectralTensor (fun i =>
          if hi : i ∈ I then
            wordComplementBasisVector (A := A) (j ⟨i, hi⟩)
          else normalizedActivityWordVector (A := A) (z ⟨i, hi⟩))
        congr 1
        funext i
        by_cases hi : i ∈ I
        · simpa [hi, j] using (Classical.choose_spec (hcomp ⟨i, hi⟩))
        · simpa [hi, z] using (Classical.choose_spec (hactivity ⟨i, hi⟩))
      rw [heq]
      exact Submodule.subset_span (Set.mem_range_self c)
    have hfspan (i : Fin n) : f i ∈ Submodule.span ℝ (u i) := by
      by_cases hi : i ∈ I
      · simpa [u, hi] using wordComplementBasisVector_mem_span
          (f i) (horth i hi)
      · have hle := wordActivitySubspace_le_span_normalizedActivityWordVector
          (A := A)
        exact (by simpa [u, hi] using hle (hact i hi))
    exact spectralTensor_mem_of_component_span P u hbase f hfspan

/-- The Hilbert-space realization of the paper's `W_l`. -/
noncomputable def spectralWeightHilbertSubspace (l : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (State A n)) :=
  (spectralWeightSubspace (A := A) (n := n) l).map
    (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).symm.toLinearMap

/-- The paper's spectral weight zero is exactly its activity space in
Hilbert coordinates. -/
theorem spectralWeightZeroHilbert_eq_activity :
    spectralWeightHilbertSubspace (A := A) (n := n) 0 =
      activityHilbertSubspace (A := A) (n := n) := by
  rw [spectralWeightHilbertSubspace,
    spectralWeightZero_eq_activitySubspace,
    activityHilbertSubspace_eq_map]

theorem mem_spectralWeightHilbertSubspace_iff
    (l : ℕ) (v : EuclideanSpace ℝ (State A n)) :
    v ∈ spectralWeightHilbertSubspace (A := A) (n := n) l ↔
      (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v ∈
        spectralWeightSubspace (A := A) (n := n) l := by
  unfold spectralWeightHilbertSubspace
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨(WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v, hv, by simp⟩

/-- The part of a spectral-weight space with complementary word factors
at exactly the positions in `I`. -/
noncomputable def spectralFactorSetSubspace (I : Finset (Fin n)) :
    Submodule ℝ (State A n → ℝ) :=
  Submodule.span ℝ {v | ∃ f : Fin n → A → ℝ,
    (∀ i ∈ I, InWordActivityOrthogonalComplement (f i)) ∧
      (∀ i ∉ I, f i ∈ wordActivitySubspace (A := A)) ∧
      v = spectralTensor f}

/-- The paper's `W_l` is the sum over all choices of the `l` complementary
word positions. -/
theorem spectralWeightSubspace_eq_iSup_factorSet (l : ℕ) :
    spectralWeightSubspace (A := A) (n := n) l =
      ⨆ I : {I : Finset (Fin n) // I.card = l},
        spectralFactorSetSubspace (A := A) (n := n) I.1 := by
  apply le_antisymm
  · unfold spectralWeightSubspace
    apply Submodule.span_le.mpr
    rintro v ⟨I, f, hcard, horth, hact, rfl⟩
    apply Submodule.mem_iSup_of_mem ⟨I, hcard⟩
    apply Submodule.subset_span
    exact ⟨f, horth, hact, rfl⟩
  · apply iSup_le
    intro I
    unfold spectralFactorSetSubspace
    apply Submodule.span_le.mpr
    rintro v ⟨f, horth, hact, rfl⟩
    apply Submodule.subset_span
    exact ⟨I.1, f, I.2, horth, hact, rfl⟩

/-- Distinct choices of complementary word positions give orthogonal
summands, even when they have the same spectral weight. -/
theorem spectralFactorSetSubspaces_orthogonal
    (I J : Finset (Fin n)) (hIJ : I ≠ J)
    (v w : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I)
    (hw : w ∈ spectralFactorSetSubspace (A := A) (n := n) J) :
    v ⬝ᵥ w = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨f, hforth, hfact, rfl⟩ := hv
      induction hw using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨g, hgorth, hgact, rfl⟩ := hw
          exact spectralTensor_dot_eq_zero_of_distinct_factorSets
            I J hIJ f g hforth hfact hgorth hgact
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul t x _ hx => simp [dotProduct_smul, hx]
  | zero => simp
  | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, zero_add]
  | smul t x _ hx => simp [smul_dotProduct, hx]

/-- The exact-factor-set summand in the Euclidean state space. -/
noncomputable def spectralFactorSetHilbertSubspace (I : Finset (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (State A n)) :=
  (spectralFactorSetSubspace (A := A) (n := n) I).map
    (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).symm.toLinearMap

theorem mem_spectralFactorSetHilbertSubspace_iff
    (I : Finset (Fin n)) (v : EuclideanSpace ℝ (State A n)) :
    v ∈ spectralFactorSetHilbertSubspace (A := A) (n := n) I ↔
      (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v ∈
        spectralFactorSetSubspace (A := A) (n := n) I := by
  unfold spectralFactorSetHilbertSubspace
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨(WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v, hv, by simp⟩

/-- The exact-factor-set summands of a fixed `W_l` form an orthogonal
family in the Euclidean state space. -/
theorem spectralFactorSetHilbertSubspaces_orthogonalFamily (l : ℕ) :
    OrthogonalFamily ℝ
      (fun I : {I : Finset (Fin n) // I.card = l} =>
        spectralFactorSetHilbertSubspace (A := A) (n := n) I.1)
      (fun I =>
        (spectralFactorSetHilbertSubspace (A := A) (n := n) I.1).subtypeₗᵢ) := by
  intro I J hIJ v w
  have hset : I.1 ≠ J.1 := fun h => hIJ (Subtype.ext h)
  have hv := (mem_spectralFactorSetHilbertSubspace_iff I.1
    (v : EuclideanSpace ℝ (State A n))).mp v.property
  have hw := (mem_spectralFactorSetHilbertSubspace_iff J.1
    (w : EuclideanSpace ℝ (State A n))).mp w.property
  rw [euclidean_inner_eq_dotProduct]
  exact spectralFactorSetSubspaces_orthogonal I.1 J.1 hset _ _ hv hw

/-- The paper's `W_l` is the orthogonal sum of its exact-factor-set
summands, now expressed in the Euclidean state space. -/
theorem spectralWeightHilbertSubspace_eq_iSup_factorSet (l : ℕ) :
    spectralWeightHilbertSubspace (A := A) (n := n) l =
      ⨆ I : {I : Finset (Fin n) // I.card = l},
        spectralFactorSetHilbertSubspace (A := A) (n := n) I.1 := by
  unfold spectralWeightHilbertSubspace spectralFactorSetHilbertSubspace
  rw [spectralWeightSubspace_eq_iSup_factorSet, Submodule.map_iSup]

private theorem submodule_iSup_exists_sum
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (p : ι → Submodule ℝ V) (v : V) (hv : v ∈ ⨆ i, p i) :
    ∃ pieces : ι → V, (∀ i, pieces i ∈ p i) ∧ v = ∑ i, pieces i := by
  classical
  refine Submodule.iSup_induction p
    (motive := fun x =>
      ∃ pieces : ι → V, (∀ i, pieces i ∈ p i) ∧ x = ∑ i, pieces i)
    hv ?_ ?_ ?_
  · intro I x hx
    refine ⟨fun J => if J = I then x else 0, ?_, ?_⟩
    · intro J
      by_cases hJI : J = I
      · simpa [hJI] using hx
      · simp [hJI]
    · simp
  · exact ⟨fun _ => 0, fun _ => Submodule.zero_mem _, by simp⟩
  · intro x y hx hy
    obtain ⟨fx, hfx, hxeq⟩ := hx
    obtain ⟨fy, hfy, hyeq⟩ := hy
    refine ⟨fun I => fx I + fy I, ?_, ?_⟩
    · intro I
      exact Submodule.add_mem _ (hfx I) (hfy I)
    · rw [hxeq, hyeq, Finset.sum_add_distrib]

/-- A linear map that preserves an orthogonal family obeys the same
norm bound on its sum as on each summand. -/
theorem orthogonalFamily_norm_le_of_summand_bounds
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (U : ι → Submodule ℝ E)
    (horth : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ))
    (T : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 ≤ c)
    (hpres : ∀ i (x : E), x ∈ U i → T x ∈ U i)
    (hbound : ∀ i (x : E), x ∈ U i → ‖T x‖ ≤ c * ‖x‖)
    (v : E) (hv : v ∈ ⨆ i, U i) : ‖T v‖ ≤ c * ‖v‖ := by
  classical
  obtain ⟨pieces, hpieces, hsum⟩ := submodule_iSup_exists_sum U v hv
  have hinput : ‖v‖ ^ 2 = ∑ i, ‖pieces i‖ ^ 2 := by
    rw [hsum]
    simpa using horth.norm_sum
      (fun i => (⟨pieces i, hpieces i⟩ : U i)) Finset.univ
  have houtput : ‖T v‖ ^ 2 = ∑ i, ‖T (pieces i)‖ ^ 2 := by
    rw [hsum, map_sum]
    simpa using horth.norm_sum
      (fun i => (⟨T (pieces i), hpres i (pieces i) (hpieces i)⟩ : U i))
      Finset.univ
  have hterms : ∑ i, ‖T (pieces i)‖ ^ 2 ≤
      c ^ 2 * ∑ i, ‖pieces i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := hbound i (pieces i) (hpieces i)
    have hci : 0 ≤ c * ‖pieces i‖ := mul_nonneg hc (norm_nonneg _)
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg (T (pieces i))) hci).mpr hi
  have hsquared : ‖T v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
    calc
      ‖T v‖ ^ 2 = ∑ i, ‖T (pieces i)‖ ^ 2 := houtput
      _ ≤ c ^ 2 * ∑ i, ‖pieces i‖ ^ 2 := hterms
      _ = c ^ 2 * ‖v‖ ^ 2 := by rw [← hinput]
      _ = (c * ‖v‖) ^ 2 := by ring
  exact le_of_sq_le_sq hsquared (mul_nonneg hc (norm_nonneg _))

/-- Fix every state word except position `i`, leaving a one-word vector.
This is the slice used to extend one-word norm estimates to a full
exact-factor-set summand. -/
def stateWordSlice (i : Fin n) (x : State A n)
    (v : State A n → ℝ) : A → ℝ :=
  fun a => v (Function.update x i a)

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
theorem stateWordSlice_spectralTensor (i : Fin n) (x : State A n)
    (f : Fin n → A → ℝ) :
    stateWordSlice i x (spectralTensor f) =
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j)) • f i := by
  classical
  funext a
  change (∏ j : Fin n, f j ((Function.update x i a) j)) =
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j)) * f i a
  rw [(Finset.mul_prod_erase Finset.univ
    (fun j : Fin n => f j ((Function.update x i a) j))
    (Finset.mem_univ i)).symm]
  simp only [Function.update_self]
  have herase :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        f j ((Function.update x i a) j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [herase]
  ring

/-- Every word slice at a complementary position remains orthogonal to
the paper's one-word activity space, even for an arbitrary vector of the
full exact-factor-set summand. -/
theorem spectralFactorSet_wordSlice_orthogonal
    (I : Finset (Fin n)) (i : Fin n) (hi : i ∈ I)
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I)
    (x : State A n) :
    InWordActivityOrthogonalComplement (stateWordSlice i x v) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨f, horth, _, rfl⟩ := hv
      rw [stateWordSlice_spectralTensor]
      intro g hg
      rw [dotProduct_smul, (horth i hi) g hg]
      simp
  | zero =>
      intro g hg
      change g ⬝ᵥ (0 : A → ℝ) = 0
      simp
  | add u v _ _ hu hv =>
      intro g hg
      change g ⬝ᵥ (stateWordSlice i x u + stateWordSlice i x v) = 0
      rw [dotProduct_add, hu g hg, hv g hg, add_zero]
  | smul t u _ hu =>
      intro g hg
      change g ⬝ᵥ (t • stateWordSlice i x u) = 0
      simp [dotProduct_smul, hu g hg]

/-- Every word slice at an activity position remains in the paper's
one-word activity space for the full exact-factor-set summand. -/
theorem spectralFactorSet_wordSlice_activity
    (I : Finset (Fin n)) (i : Fin n) (hi : i ∉ I)
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I)
    (x : State A n) :
    stateWordSlice i x v ∈ wordActivitySubspace (A := A) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨f, _, hact, rfl⟩ := hv
      rw [stateWordSlice_spectralTensor]
      exact Submodule.smul_mem _ _ (hact i hi)
  | zero =>
      exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      change stateWordSlice i x u + stateWordSlice i x v ∈ _
      exact Submodule.add_mem _ hu hv
  | smul t u _ hu =>
      change t • stateWordSlice i x u ∈ _
      exact Submodule.smul_mem _ t hu

/-- Apply a one-word matrix in one chosen state coordinate. -/
def applyWordMatrixAt (D : Matrix A A ℝ) (i : Fin n)
    (v : State A n → ℝ) : State A n → ℝ :=
  fun x => ∑ a : A, D (x i) a * v (Function.update x i a)

omit [AddCommGroup A] [DecidableEq A] in
/-- Taking a word slice commutes with applying the one-word matrix at
that position. -/
theorem stateWordSlice_applyWordMatrixAt
    (D : Matrix A A ℝ) (i : Fin n) (x : State A n)
    (v : State A n → ℝ) :
    stateWordSlice i x (applyWordMatrixAt D i v) =
      D *ᵥ stateWordSlice i x v := by
  classical
  funext b
  change (∑ a : A, D ((Function.update x i b) i) a *
      v (Function.update (Function.update x i b) i a)) =
    ∑ a : A, D b a * v (Function.update x i a)
  simp

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- A word slice evaluated at the original word recovers the original
state coordinate. -/
theorem stateWordSlice_originalWord (i : Fin n) (x : State A n)
    (v : State A n → ℝ) :
    stateWordSlice i x v (x i) = v x := by
  simp [stateWordSlice]

/-- Reassemble a state from its word at `i` and all its other words. -/
def stateWithWord (i : Fin n) (a : A)
    (rest : {j : Fin n // j ≠ i} → A) : State A n :=
  (Equiv.funSplitAt i A).symm (a, rest)

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
theorem stateWithWord_update (i : Fin n) (a b : A)
    (rest : {j : Fin n // j ≠ i} → A) :
    Function.update (stateWithWord i a rest) i b =
      stateWithWord i b rest := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [stateWithWord, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [stateWithWord, Equiv.funSplitAt, Equiv.piSplitAt, hji]

omit [DecidableEq A] in
/-- The squared coordinate sum of a state function splits into a sum of
one-word squared coordinate sums, one for each choice of the other words. -/
theorem sum_state_sq_eq_sum_wordSlices (i : Fin n)
    (v : State A n → ℝ) :
    (∑ x : State A n, v x ^ 2) =
      ∑ rest : ({j : Fin n // j ≠ i} → A),
        ∑ a : A, (stateWordSlice i (stateWithWord i 0 rest) v a) ^ 2 := by
  classical
  let e := Equiv.funSplitAt i A
  calc
    (∑ x : State A n, v x ^ 2) =
        ∑ p : A × ({j : Fin n // j ≠ i} → A), v (e.symm p) ^ 2 := by
          exact Fintype.sum_equiv e _ _
            (fun x => (congrArg (fun y => v y ^ 2) (e.symm_apply_apply x)).symm)
    _ = ∑ rest : ({j : Fin n // j ≠ i} → A),
          ∑ a : A, v (stateWithWord i a rest) ^ 2 := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            rfl
    _ = _ := by
      congr 1
      funext rest
      congr 1
      funext a
      rw [stateWordSlice, stateWithWord_update]

omit [DecidableEq A] in
/-- The Euclidean norm of a state function is the sum of the squared
Euclidean norms of its one-word slices. -/
theorem state_norm_sq_eq_sum_wordSlice_norm_sq (i : Fin n)
    (v : State A n → ℝ) :
    ‖WithLp.toLp 2 v‖ ^ 2 =
      ∑ rest : ({j : Fin n // j ≠ i} → A),
        ‖WithLp.toLp 2
          (stateWordSlice i (stateWithWord i 0 rest) v)‖ ^ 2 := by
  calc
    ‖WithLp.toLp 2 v‖ ^ 2 = ∑ x : State A n, v x ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v)
    _ = ∑ rest : ({j : Fin n // j ≠ i} → A),
          ∑ a : A,
            (stateWordSlice i (stateWithWord i 0 rest) v a) ^ 2 :=
      sum_state_sq_eq_sum_wordSlices i v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro rest _
      symm
      simpa only [Real.norm_eq_abs, sq_abs] using
        EuclideanSpace.norm_sq_eq
          (WithLp.toLp 2 (stateWordSlice i (stateWithWord i 0 rest) v))

omit [DecidableEq A] in
/-- A one-word matrix bound on every slice gives the same bound for its
action in that state coordinate. -/
theorem applyWordMatrixAt_norm_le_of_slice_bounds
    (D : Matrix A A ℝ) (i : Fin n) (v : State A n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hcontract : ∀ x : State A n,
      ‖WithLp.toLp 2 (D *ᵥ stateWordSlice i x v)‖ ≤
        c * ‖WithLp.toLp 2 (stateWordSlice i x v)‖) :
    ‖WithLp.toLp 2 (applyWordMatrixAt D i v)‖ ≤
      c * ‖WithLp.toLp 2 v‖ := by
  let u := applyWordMatrixAt D i v
  have hterms :
      (∑ rest : ({j : Fin n // j ≠ i} → A),
        ‖WithLp.toLp 2
          (stateWordSlice i (stateWithWord i 0 rest) u)‖ ^ 2) ≤
      c ^ 2 *
        ∑ rest : ({j : Fin n // j ≠ i} → A),
          ‖WithLp.toLp 2
            (stateWordSlice i (stateWithWord i 0 rest) v)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro rest _
    have h := hcontract (stateWithWord i 0 rest)
    have h' :
        ‖WithLp.toLp 2
          (stateWordSlice i (stateWithWord i 0 rest) u)‖ ≤
        c * ‖WithLp.toLp 2
          (stateWordSlice i (stateWithWord i 0 rest) v)‖ := by
      simpa only [u, stateWordSlice_applyWordMatrixAt] using h
    have hc' : 0 ≤ c * ‖WithLp.toLp 2
        (stateWordSlice i (stateWithWord i 0 rest) v)‖ :=
      mul_nonneg hc (norm_nonneg _)
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) hc').mpr h'
  have hsquared :
      ‖WithLp.toLp 2 u‖ ^ 2 ≤
        (c * ‖WithLp.toLp 2 v‖) ^ 2 := by
    calc
      ‖WithLp.toLp 2 u‖ ^ 2 =
          ∑ rest : ({j : Fin n // j ≠ i} → A),
            ‖WithLp.toLp 2
              (stateWordSlice i (stateWithWord i 0 rest) u)‖ ^ 2 :=
        state_norm_sq_eq_sum_wordSlice_norm_sq i u
      _ ≤ c ^ 2 *
          ∑ rest : ({j : Fin n // j ≠ i} → A),
            ‖WithLp.toLp 2
              (stateWordSlice i (stateWithWord i 0 rest) v)‖ ^ 2 := hterms
      _ = c ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
        rw [← state_norm_sq_eq_sum_wordSlice_norm_sq i v]
      _ = (c * ‖WithLp.toLp 2 v‖) ^ 2 := by ring
  exact le_of_sq_le_sq hsquared (mul_nonneg hc (norm_nonneg _))

omit [AddCommGroup A] [Fintype A] [DecidableEq A] in
/-- Factor one coordinate out of a pure tensor. -/
theorem spectralTensor_factorWord (i : Fin n) (x : State A n)
    (f : Fin n → A → ℝ) :
    spectralTensor f x = f i (x i) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun j : Fin n => f j (x j)) (Finset.mem_univ i)).symm

omit [AddCommGroup A] [DecidableEq A] in
/-- A one-word matrix acts on exactly one factor of a pure tensor. -/
theorem applyWordMatrixAt_spectralTensor
    (D : Matrix A A ℝ) (i : Fin n) (f : Fin n → A → ℝ) :
    applyWordMatrixAt D i (spectralTensor f) =
      spectralTensor (Function.update f i (D *ᵥ f i)) := by
  classical
  funext x
  let r : ℝ := ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j (x j)
  have hstate (a : A) :
      spectralTensor f (Function.update x i a) = f i a * r := by
    have h := congrFun (stateWordSlice_spectralTensor i x f) a
    simpa [stateWordSlice, r, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have herase :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (Function.update f i (D *ᵥ f i)) j (x j)) = r := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hright :
      spectralTensor (Function.update f i (D *ᵥ f i)) x =
        (D *ᵥ f i) (x i) * r := by
    rw [spectralTensor_factorWord, Function.update_self, herase]
  change (∑ a : A, D (x i) a *
      spectralTensor f (Function.update x i a)) =
    spectralTensor (Function.update f i (D *ᵥ f i)) x
  rw [hright]
  simp_rw [hstate]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rfl

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrixAt_add (D : Matrix A A ℝ) (i : Fin n)
    (v w : State A n → ℝ) :
    applyWordMatrixAt D i (v + w) =
      applyWordMatrixAt D i v + applyWordMatrixAt D i w := by
  classical
  funext x
  simp [applyWordMatrixAt, mul_add, Finset.sum_add_distrib]

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrixAt_smul (D : Matrix A A ℝ) (i : Fin n)
    (c : ℝ) (v : State A n → ℝ) :
    applyWordMatrixAt D i (c • v) = c • applyWordMatrixAt D i v := by
  classical
  funext x
  simp [applyWordMatrixAt, Finset.mul_sum, mul_left_comm]

/-- Apply the same one-word matrix successively at the listed word
positions, in list order. -/
def applyWordMatrices (D : Matrix A A ℝ) :
    List (Fin n) → (State A n → ℝ) → State A n → ℝ
  | [], v => v
  | i :: is, v => applyWordMatrices D is (applyWordMatrixAt D i v)

/-- The corresponding list of updates to pure-tensor factors. -/
def updateWordFactors (D : Matrix A A ℝ) :
    List (Fin n) → (Fin n → A → ℝ) → Fin n → A → ℝ
  | [], f => f
  | i :: is, f => updateWordFactors D is (Function.update f i (D *ᵥ f i))

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrices_spectralTensor
    (D : Matrix A A ℝ) (is : List (Fin n))
    (f : Fin n → A → ℝ) :
    applyWordMatrices D is (spectralTensor f) =
      spectralTensor (updateWordFactors D is f) := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
      change applyWordMatrices D is
        (applyWordMatrixAt D i (spectralTensor f)) = _
      rw [applyWordMatrixAt_spectralTensor]
      exact ih (Function.update f i (D *ᵥ f i))

omit [AddCommGroup A] [DecidableEq A] in
/-- Updating each word position at most once applies `D` precisely to
the factors at positions in the list. -/
theorem updateWordFactors_of_nodup
    (D : Matrix A A ℝ) (is : List (Fin n)) (his : is.Nodup)
    (f : Fin n → A → ℝ) (j : Fin n) :
    updateWordFactors D is f j =
      if j ∈ is then D *ᵥ f j else f j := by
  induction is generalizing f with
  | nil => simp [updateWordFactors]
  | cons i is ih =>
      have hinot : i ∉ is := (List.nodup_cons.mp his).1
      have htail : is.Nodup := (List.nodup_cons.mp his).2
      change updateWordFactors D is
        (Function.update f i (D *ᵥ f i)) j = _
      rw [ih htail]
      by_cases hji : j = i
      · subst j
        simp [hinot]
      · simp [hji]

omit [AddCommGroup A] [DecidableEq A] in
/-- Applying a one-word matrix once in every state coordinate agrees
with its tensor action on every pure tensor. -/
theorem applyWordMatrices_finRange_spectralTensor
    (D : Matrix A A ℝ) (f : Fin n → A → ℝ) :
    applyWordMatrices D (List.finRange n) (spectralTensor f) =
      spectralTensor (fun i => D *ᵥ f i) := by
  rw [applyWordMatrices_spectralTensor]
  congr 1
  funext i
  rw [updateWordFactors_of_nodup D (List.finRange n)
    (List.nodup_finRange n) f i]
  simp [List.mem_finRange]

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrices_add (D : Matrix A A ℝ)
    (is : List (Fin n)) (v w : State A n → ℝ) :
    applyWordMatrices D is (v + w) =
      applyWordMatrices D is v + applyWordMatrices D is w := by
  induction is generalizing v w with
  | nil => rfl
  | cons i is ih =>
      change applyWordMatrices D is (applyWordMatrixAt D i (v + w)) =
        applyWordMatrices D is (applyWordMatrixAt D i v) +
          applyWordMatrices D is (applyWordMatrixAt D i w)
      rw [applyWordMatrixAt_add, ih]

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrices_smul (D : Matrix A A ℝ)
    (is : List (Fin n)) (c : ℝ) (v : State A n → ℝ) :
    applyWordMatrices D is (c • v) =
      c • applyWordMatrices D is v := by
  induction is generalizing v with
  | nil => rfl
  | cons i is ih =>
      change applyWordMatrices D is (applyWordMatrixAt D i (c • v)) =
        c • applyWordMatrices D is (applyWordMatrixAt D i v)
      rw [applyWordMatrixAt_smul, ih]

omit [AddCommGroup A] [DecidableEq A] in
theorem applyWordMatrices_zero (D : Matrix A A ℝ)
    (is : List (Fin n)) :
    applyWordMatrices D is (0 : State A n → ℝ) = 0 := by
  have h := applyWordMatrices_smul D is (0 : ℝ) (0 : State A n → ℝ)
  simpa using h

/-- The list of all state positions contains exactly `I.card`
complementary positions. -/
theorem finRange_countP_mem_eq_card (I : Finset (Fin n)) :
    (List.finRange n).countP (fun i => i ∈ I) = I.card := by
  classical
  let L := (List.finRange n).filter (fun i => i ∈ I)
  have hnodup : L.Nodup := (List.nodup_finRange n).filter _
  have hset : L.toFinset = I := by
    ext i
    simp [L]
  calc
    (List.finRange n).countP (fun i => i ∈ I) = L.length := by
      rw [List.countP_eq_length_filter]
    _ = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = I.card := by rw [hset]

/-- The sum of a finite set of the paper's spectral-weight spaces. This
notation is useful for the high-weight tails in the proof of Theorem 3. -/
noncomputable def spectralWeightIndexSetHilbertSubspace (J : Finset ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (State A n)) :=
  ⨆ l : {l : ℕ // l ∈ J},
    spectralWeightHilbertSubspace (A := A) (n := n) l.1

/-- Reindex the paper's positive spectral sum by its literal weights
`1, ..., n`, so high-weight tails can be expressed with finite intervals. -/
theorem positiveSpectralSubspace_eq_weightIndexSet :
    positiveSpectralSubspace (A := A) (n := n) =
      ⨆ l : {l : ℕ // l ∈ Finset.Icc 1 n},
        spectralWeightSubspace (A := A) (n := n) l.1 := by
  apply le_antisymm
  · unfold positiveSpectralSubspace
    apply iSup_le
    intro i
    have hi : i.1 + 1 ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    exact le_iSup_of_le (⟨i.1 + 1, hi⟩ :
      {l : ℕ // l ∈ Finset.Icc 1 n}) le_rfl
  · apply iSup_le
    intro l
    have hi : l.1 - 1 < n := by
      have h := (Finset.mem_Icc.mp l.2)
      omega
    have heq : (l.1 - 1) + 1 = l.1 := by
      have h := (Finset.mem_Icc.mp l.2)
      omega
    change spectralWeightSubspace (A := A) (n := n) l.1 ≤
      positiveSpectralSubspace (A := A) (n := n)
    unfold positiveSpectralSubspace
    simpa only [heq] using
      (le_iSup (fun i : Fin n =>
        spectralWeightSubspace (A := A) (n := n) (i.1 + 1))
        (⟨l.1 - 1, hi⟩ : Fin n))

/-- The full positive-weight sum is exactly the activity orthogonal
complement, now in the finite-index form used for tail estimates. -/
theorem spectralWeightIndexSet_Icc_one_eq_activityOrthogonal :
    spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
      (Finset.Icc 1 n) =
      (activityHilbertSubspace (A := A) (n := n))ᗮ := by
  let E := EuclideanSpace ℝ (State A n)
  let e := (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).symm
  have hmap : (positiveSpectralSubspace (A := A) (n := n)).map
      e.toLinearMap =
      (activityHilbertSubspace (A := A) (n := n))ᗮ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_positiveSpectralSubspace_iff_mem_activityHilbertOrthogonal
        (e w)).mp (by simpa [e] using hw)
    · intro hv
      exact ⟨(WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v,
        (mem_positiveSpectralSubspace_iff_mem_activityHilbertOrthogonal v).mpr hv,
        by simp [e]⟩
  rw [← hmap, positiveSpectralSubspace_eq_weightIndexSet,
    Submodule.map_iSup]
  rfl

/-- The two mixed activity blocks are Hilbert adjoints after transposing
the difference-distribution matrix. -/
theorem activityComplementToActivityOperator_transpose_eq_adjoint
    (D : Matrix (State A n) (State A n) ℝ) :
    activityComplementToActivityOperator Dᵀ =
      ContinuousLinearMap.adjoint (activityToComplementOperator D) := by
  let K := activityHilbertSubspace (A := A) (n := n)
  let Q := Kᗮ
  have hmatrix : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Dᵀ =
      ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D) := by
    have hstar : star D = Dᵀ := by
      rw [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hstar, map_star, ContinuousLinearMap.star_eq_adjoint]
  change (K.orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Dᵀ ∘L
      Q.subtypeL) =
    ContinuousLinearMap.adjoint
      (Q.orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L K.subtypeL)
  rw [hmatrix]
  simp only [ContinuousLinearMap.adjoint_comp,
    K.adjoint_subtypeL, Q.adjoint_orthogonalProjection]
  ext x
  rfl

section SpectralGramNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem spectral_weighted_abs_sum_sq_le
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ι → ℝ) :
    (∑ i : ι, w i * |x i|) ^ 2 ≤
      (∑ i : ι, w i) * (∑ i : ι, w i * (x i) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := Finset.univ)
    (r := fun i => w i * |x i|)
    (f := w) (g := fun i => w i * (x i) ^ 2)
  · intro i _
    exact hw i
  · intro i _
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _
    rw [mul_pow, sq_abs]
    ring

set_option maxHeartbeats 1000000 in
/-- A finite real matrix has Euclidean operator norm bounded by a common absolute row and column sum. -/
theorem matrix_twoNorm_le_rowColumnAbsSum
    (M : Matrix ι ι ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j : ι, |M i j|) ≤ C)
    (hcol : ∀ j, (∑ i : ι, |M i j|) ≤ C) :
    ‖M‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := ι) (n := ι) ≪≫ₗ
      LinearMap.toContinuousLinearMap) M
  change ‖T‖ ≤ C
  have hT (x : EuclideanSpace ℝ ι) : ‖T x‖ ≤ C * ‖x‖ := by
    have hpoint (i : ι) :
        ((M *ᵥ x) i) ^ 2 ≤
          C * (∑ j : ι, |M i j| * (x j) ^ 2) := by
      have habs :
          |(M *ᵥ x) i| ≤ ∑ j : ι, |M i j| * |x j| := by
        simpa only [Matrix.mulVec, dotProduct, abs_mul] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun j : ι => M i j * x j))
      have hweight := spectral_weighted_abs_sum_sq_le
        (fun j => |M i j|) (fun j => abs_nonneg _) (fun j => x j)
      have hsq : ((M *ᵥ x) i) ^ 2 ≤
          (∑ j : ι, |M i j| * |x j|) ^ 2 := by
        have hnonneg : 0 ≤ ∑ j : ι, |M i j| * |x j| :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have hprod := mul_nonneg (sub_nonneg.mpr habs)
          (add_nonneg (abs_nonneg ((M *ᵥ x) i)) hnonneg)
        nlinarith [sq_abs ((M *ᵥ x) i)]
      calc
        ((M *ᵥ x) i) ^ 2 ≤
            (∑ j : ι, |M i j| * |x j|) ^ 2 := hsq
        _ ≤ (∑ j : ι, |M i j|) *
            (∑ j : ι, |M i j| * (x j) ^ 2) := hweight
        _ ≤ C * (∑ j : ι, |M i j| * (x j) ^ 2) := by
          gcongr
          exact hrow i
    have hsq : ‖((EuclideanSpace.equiv ι ℝ).symm <| M *ᵥ x)‖ ^ 2 ≤
        C ^ 2 * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      change (∑ i : ι, ‖(M *ᵥ x) i‖ ^ 2) ≤
        C ^ 2 * ∑ i : ι, ‖x i‖ ^ 2
      simp only [Real.norm_eq_abs, sq_abs]
      calc
        (∑ i : ι, ((M *ᵥ x) i) ^ 2) ≤
            ∑ i : ι, C * (∑ j : ι, |M i j| * (x j) ^ 2) := by
          gcongr with i
          exact hpoint i
        _ = C * ∑ j : ι, (x j) ^ 2 * (∑ i : ι, |M i j|) := by
          calc
            (∑ i : ι, C * (∑ j : ι, |M i j| * (x j) ^ 2)) =
                C * ∑ i : ι, ∑ j : ι, |M i j| * (x j) ^ 2 := by
                  rw [Finset.mul_sum]
            _ = C * ∑ j : ι, ∑ i : ι, |M i j| * (x j) ^ 2 := by
              rw [Finset.sum_comm]
            _ = C * ∑ j : ι, (x j) ^ 2 * (∑ i : ι, |M i j|) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ C * ∑ j : ι, (x j) ^ 2 * C := by
          gcongr with j
          exact hcol j
        _ = C ^ 2 * ∑ j : ι, (x j) ^ 2 := by
          rw [← Finset.sum_mul]
          ring
    change ‖((EuclideanSpace.equiv ι ℝ).symm <| M *ᵥ x)‖ ≤ C * ‖x‖
    have hCx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
    nlinarith [norm_nonneg ((EuclideanSpace.equiv ι ℝ).symm <| M *ᵥ x), hCx]
  exact T.opNorm_le_bound hC hT

/-- The absolute row sum of a dependent block diagonal matrix comes from its one occupied block. -/
theorem matrix_blockDiagonal_rowAbsSum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {β : κ → Type*} [∀ i, Fintype (β i)]
    (F : ∀ i, Matrix (β i) (β i) ℝ) (x : Sigma β) :
    (∑ y : Sigma β, |(Matrix.blockDiagonal' F) x y|) =
      ∑ y : β x.1, |F x.1 x.2 y| := by
  rcases x with ⟨i, xi⟩
  rw [Fintype.sum_sigma]
  simp only [Matrix.blockDiagonal'_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

set_option maxHeartbeats 1000000 in
/-- Each row of a fixed-position spectral Gram inverse has the paper's exact absolute sum. -/
theorem spectralGramBlockKernel_inverse_rowAbsSum
    (I : Finset (Fin n)) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : SpectralGramBlockIndex (A := A) I) :
    (∑ y : SpectralGramBlockIndex (A := A) I,
      |((spectralGramBlockKernel (A := A) I r)⁻¹) x y|) =
      ((1 - r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ := by
  have hq : 0 < 1 - r ^ 2 := by nlinarith
  rw [spectralGramBlockKernel_inverse I r (ne_of_gt hq)]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have ht : 0 ≤ ((1 - r ^ 2) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ :=
    (inv_nonneg.mpr (pow_nonneg hq.le _))
  simp_rw [abs_mul, abs_of_nonneg ht]
  rw [← Finset.mul_sum]
  rw [show (∑ y : SpectralGramBlockIndex (A := A) I,
      |spectralGramBlockKernel (A := A) I (-r) x y|) =
      (1 + r) ^ Fintype.card {i : Fin n // i ∉ I} from ?_]
  · have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [hfactor, mul_pow, mul_inv_rev]
    have hpos : (1 + r) ^ Fintype.card {i : Fin n // i ∉ I} ≠ 0 :=
      ne_of_gt (pow_pos (by linarith : 0 < 1 + r) _)
    have hminus : (1 - r) ^ Fintype.card {i : Fin n // i ∉ I} ≠ 0 :=
      ne_of_gt (pow_pos (by linarith : 0 < 1 - r) _)
    calc
      ((1 + r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ *
          ((1 - r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ *
          (1 + r) ^ Fintype.card {i : Fin n // i ∉ I} =
          ((1 - r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ *
            (((1 + r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ *
              (1 + r) ^ Fintype.card {i : Fin n // i ∉ I}) := by ring
      _ = ((1 - r) ^ Fintype.card {i : Fin n // i ∉ I})⁻¹ := by
        rw [inv_mul_cancel₀ hpos, mul_one]
  · rcases x with ⟨j,z⟩
    rw [Fintype.sum_prod_type]
    simp only [spectralGramBlockKernel_apply, abs_mul, abs_ite,
      abs_one, abs_zero]
    simp only [ite_mul, one_mul, zero_mul]
    simpa using (spectralActivityGramKernel_negative_rowAbsSum
      (ι := {i : Fin n // i ∉ I}) r hr0 z)

set_option maxHeartbeats 1000000 in
/-- The full spectral Gram inverse has the paper's `(1 - 1/√q)^(-(n-l))` two-norm bound. -/
theorem spectralBasisMatrix_gram_inverse_twoNorm_le
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    ‖(((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l)⁻¹)‖ ≤
        ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l))⁻¹ := by
  let r : ℝ := (Real.sqrt (Fintype.card A : ℝ))⁻¹
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩
  have hq : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
  have hsqrt : 1 < Real.sqrt (Fintype.card A : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity)).mpr hsqrt
  let B := spectralBasisMatrix (A := A) (n := n) l
  let M : Matrix (SpectralBasisIndex (A := A) (n := n) l)
    (SpectralBasisIndex (A := A) (n := n) l) ℝ := (Bᵀ * B)⁻¹
  have hrow (x : SpectralBasisIndex (A := A) (n := n) l) :
      (∑ y, |M x y|) ≤ ((1 - r) ^ (n - l))⁻¹ := by
    rw [show M = Matrix.blockDiagonal'
        (fun I : {I : Finset (Fin n) // I.card = l} =>
          (spectralBasisMatrix_gramBlockFamily (A := A) l I)⁻¹) from
        spectralBasisMatrix_gram_inverse l u hu]
    rw [matrix_blockDiagonal_rowAbsSum]
    rcases x with ⟨I,x⟩
    change (∑ y : SpectralGramBlockIndex (A := A) I.1,
      |((spectralGramBlockKernel (A := A) I.1 r)⁻¹) x y|) ≤ _
    rw [spectralGramBlockKernel_inverse_rowAbsSum I.1 r hr0 hr1 x]
    simp [I.property, r]
  have hsym : Mᵀ = M := by
    dsimp [M]
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hcol (y : SpectralBasisIndex (A := A) (n := n) l) :
      (∑ x, |M x y|) ≤ ((1 - r) ^ (n - l))⁻¹ := by
    calc
      (∑ x, |M x y|) = ∑ x, |M y x| := by
        apply Finset.sum_congr rfl
        intro x _
        have hh := congrFun (congrFun hsym y) x
        simpa only [Matrix.transpose_apply] using congrArg abs hh
      _ ≤ ((1 - r) ^ (n - l))⁻¹ := hrow y
  have hC : 0 ≤ ((1 - r) ^ (n - l))⁻¹ :=
    (inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hr1.le) _))
  change ‖M‖ ≤ _
  simpa only [r] using matrix_twoNorm_le_rowColumnAbsSum M
    _ hC hrow hcol

end SpectralGramNorm

open scoped Matrix.Norms.L2Operator in
/-- The paper's spectral squared-entry count bounds the Euclidean norm of the raw rectangular `Bₗ₁ᵀ D_L Bₗ₂` matrix. -/
theorem spectralBasisMatrix_linear_twoNorm_le_paperSum
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂‖ ≤
    Real.sqrt ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
      ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
        (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
          (if k < n ∧ n < k + l₁ + l₂ then
            ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
              (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
          else 0)) := by
  let M := (spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂
  calc
    ‖M‖ ≤ Real.sqrt (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂, (M c d) ^ 2) :=
        matrixTwoNorm_le_sqrt_sum_entries_sq_rectangular M
    _ ≤ _ := Real.sqrt_le_sqrt
      (hMDS.spectralBasisMatrix_fullFrobenius_sum_squares_le L l₁ l₂ hpos hd)

/-- The full spectral Gram matrix multiplied by its exact inverse is the identity. -/
theorem spectralBasisMatrix_gram_mul_inverse
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l) *
      (((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
        spectralBasisMatrix (A := A) (n := n) l)⁻¹) = 1 := by
  classical
  let r : ℝ := (Real.sqrt (Fintype.card A : ℝ))⁻¹
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩
  have hq : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
  have hsqrt : 1 < Real.sqrt (Fintype.card A : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by positivity)).mpr hsqrt
  have hr : 1 - r ^ 2 ≠ 0 := by
    have hsq : r ^ 2 < 1 := by nlinarith
    exact ne_of_gt (sub_pos.mpr hsq)
  have hblock (I : {I : Finset (Fin n) // I.card = l}) :
      spectralBasisMatrix_gramBlockFamily (A := A) l I *
        (spectralBasisMatrix_gramBlockFamily (A := A) l I)⁻¹ = 1 := by
    exact spectralGramBlockKernel_mul_inverse I.1 r hr
  rw [spectralBasisMatrix_gram_inverse l u hu,
    spectralBasisMatrix_gram_eq_blockDiagonal]
  rw [← Matrix.blockDiagonal'_mul]
  simp_rw [hblock]
  exact Matrix.blockDiagonal'_one

/-- The paper's spectral Gram matrix is positive definite, enabling orthonormalization of `Bₗ`. -/
theorem spectralBasisMatrix_gram_posDef
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
      spectralBasisMatrix (A := A) (n := n) l).PosDef := by
  let B := spectralBasisMatrix (A := A) (n := n) l
  let G := Bᵀ * B
  have hsem : G.PosSemidef := by
    simpa [G, Matrix.conjTranspose] using
      (Matrix.posSemidef_conjTranspose_mul_self B)
  have hunit : IsUnit G :=
    Matrix.isUnit_of_right_inverse (spectralBasisMatrix_gram_mul_inverse l u hu)
  exact hsem.posDef_iff_isUnit.mpr hunit

/-- The inverse square root of the paper's positive-definite spectral Gram matrix. -/
noncomputable def spectralGramInverseSquareRoot
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    Matrix (SpectralBasisIndex (A := A) (n := n) l)
      (SpectralBasisIndex (A := A) (n := n) l) ℝ :=
  (spectralBasisMatrix_gram_posDef l u hu).posSemidef.sqrt⁻¹

/-- The inverse square root orthonormalizes the paper's spectral basis. -/
theorem spectralGramInverseSquareRoot_orthonormal
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    (spectralGramInverseSquareRoot (n := n) l u hu)ᵀ *
      ((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
        spectralBasisMatrix (A := A) (n := n) l) *
        spectralGramInverseSquareRoot (n := n) l u hu = 1 := by
  let G := (spectralBasisMatrix (A := A) (n := n) l)ᵀ *
    spectralBasisMatrix (A := A) (n := n) l
  let hG : G.PosDef := spectralBasisMatrix_gram_posDef l u hu
  let H := hG.posSemidef.sqrt
  have hHunit : IsUnit H := hG.posDef_sqrt.isUnit
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hHunit
  have hHtranspose : Hᵀ = H := by
    simpa [Matrix.conjTranspose] using hG.posSemidef.posSemidef_sqrt.1.eq
  have hHsq : H * H = G := hG.posSemidef.sqrt_mul_self
  change (H⁻¹)ᵀ * G * H⁻¹ = 1
  rw [Matrix.transpose_nonsing_inv, hHtranspose, ← hHsq]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul H hHdet,
    Matrix.mul_nonsing_inv H hHdet]

/-- Its squared Euclidean operator norm is the norm of the inverse spectral Gram matrix. -/
theorem spectralGramInverseSquareRoot_twoNorm_sq
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    ‖spectralGramInverseSquareRoot (n := n) l u hu‖ ^ 2 =
      ‖(((spectralBasisMatrix (A := A) (n := n) l)ᵀ *
        spectralBasisMatrix (A := A) (n := n) l)⁻¹)‖ := by
  let G := (spectralBasisMatrix (A := A) (n := n) l)ᵀ *
    spectralBasisMatrix (A := A) (n := n) l
  let hG : G.PosDef := spectralBasisMatrix_gram_posDef l u hu
  let H := hG.posSemidef.sqrt
  have hHtranspose : Hᵀ = H := by
    simpa [Matrix.conjTranspose] using hG.posSemidef.posSemidef_sqrt.1.eq
  have hRtranspose : (H⁻¹)ᵀ = H⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hHtranspose]
  have hR2 : H⁻¹ * H⁻¹ = G⁻¹ := by
    rw [← Matrix.mul_inv_rev, hG.posSemidef.sqrt_mul_self]
  change ‖H⁻¹‖ ^ 2 = ‖G⁻¹‖
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self]
  simpa [Matrix.conjTranspose, hRtranspose] using congrArg norm hR2

/-- The paper's orthonormalized spectral matrix `Cₗ = Bₗ Rₗ`. -/
noncomputable def spectralOrthonormalBasisMatrix
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    Matrix (State A n) (SpectralBasisIndex (A := A) (n := n) l) ℝ :=
  spectralBasisMatrix (A := A) (n := n) l *
    spectralGramInverseSquareRoot (n := n) l u hu

/-- The columns of the normalized spectral matrix are orthonormal. -/
theorem spectralOrthonormalBasisMatrix_orthonormal
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    (spectralOrthonormalBasisMatrix (n := n) l u hu)ᵀ *
      spectralOrthonormalBasisMatrix (n := n) l u hu = 1 := by
  simpa [spectralOrthonormalBasisMatrix, Matrix.transpose_mul,
    Matrix.mul_assoc] using
      spectralGramInverseSquareRoot_orthonormal (n := n) l u hu

/-- Compression from raw spectral coordinates to the orthonormal spectral coordinates loses one inverse-square-root Gram factor on each side. -/
theorem spectralOrthonormalBasisMatrix_compression_twoNorm_le
    (l₁ l₂ : ℕ) (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
      spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ ≤
      ‖spectralGramInverseSquareRoot (n := n) l₁ u hu‖ *
        ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ * M *
          spectralBasisMatrix (A := A) (n := n) l₂‖ *
        ‖spectralGramInverseSquareRoot (n := n) l₂ u hu‖ := by
  let B₁ := spectralBasisMatrix (A := A) (n := n) l₁
  let B₂ := spectralBasisMatrix (A := A) (n := n) l₂
  let R₁ := spectralGramInverseSquareRoot (n := n) l₁ u hu
  let R₂ := spectralGramInverseSquareRoot (n := n) l₂ u hu
  let Δ := B₁ᵀ * M * B₂
  have hRt : ‖R₁ᵀ‖ = ‖R₁‖ := by
    simpa [Matrix.conjTranspose] using Matrix.l2_opNorm_conjTranspose R₁
  have hmatrix : (B₁ * R₁)ᵀ * M * (B₂ * R₂) = R₁ᵀ * Δ * R₂ := by
    simp [Δ, Matrix.transpose_mul, Matrix.mul_assoc]
  change ‖(B₁ * R₁)ᵀ * M * (B₂ * R₂)‖ ≤ ‖R₁‖ * ‖Δ‖ * ‖R₂‖
  rw [hmatrix]
  calc
    ‖R₁ᵀ * Δ * R₂‖ ≤ ‖R₁ᵀ * Δ‖ * ‖R₂‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖R₁ᵀ‖ * ‖Δ‖) * ‖R₂‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖R₁‖ * ‖Δ‖ * ‖R₂‖ := by rw [hRt]

/-- The paper's explicit inverse-Gram bound converts raw spectral coordinates to orthonormal spectral coordinates for any matrix. -/
theorem spectralOrthonormalBasisMatrix_compression_twoNorm_le_gramBound
    (l₁ l₂ : ℕ) (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
      spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ ≤
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ * M *
          spectralBasisMatrix (A := A) (n := n) l₂‖ *
        Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let R₁ := spectralGramInverseSquareRoot (n := n) l₁ u hu
  let R₂ := spectralGramInverseSquareRoot (n := n) l₂ u hu
  let Δ := (spectralBasisMatrix (A := A) (n := n) l₁)ᵀ * M *
    spectralBasisMatrix (A := A) (n := n) l₂
  let C (l : ℕ) : ℝ :=
    ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l))⁻¹
  have hC₁ : 0 ≤ C l₁ := by
    dsimp [C]
    have hq : (1 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩)
    have hs : 1 < Real.sqrt (Fintype.card A : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hq
    have hr : (Real.sqrt (Fintype.card A : ℝ))⁻¹ < 1 :=
      (inv_lt_one₀ (by positivity)).mpr hs
    exact inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hr.le) _)
  have hC₂ : 0 ≤ C l₂ := by
    dsimp [C]
    have hq : (1 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩)
    have hs : 1 < Real.sqrt (Fintype.card A : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hq
    have hr : (Real.sqrt (Fintype.card A : ℝ))⁻¹ < 1 :=
      (inv_lt_one₀ (by positivity)).mpr hs
    exact inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hr.le) _)
  have hR₁ : ‖R₁‖ ≤ Real.sqrt (C l₁) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hC₁, spectralGramInverseSquareRoot_twoNorm_sq]
    exact spectralBasisMatrix_gram_inverse_twoNorm_le l₁ u hu
  have hR₂ : ‖R₂‖ ≤ Real.sqrt (C l₂) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hC₂, spectralGramInverseSquareRoot_twoNorm_sq]
    exact spectralBasisMatrix_gram_inverse_twoNorm_le l₂ u hu
  calc
    ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
      spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ ≤
      ‖R₁‖ * ‖Δ‖ * ‖R₂‖ :=
        spectralOrthonormalBasisMatrix_compression_twoNorm_le l₁ l₂ u hu M
    _ ≤ Real.sqrt (C l₁) * ‖Δ‖ * Real.sqrt (C l₂) := by
      gcongr
    _ = _ := rfl

/-- The paper's spectral MDS count, including both Gram losses, bounds the rectangular matrix between the orthonormal `Wₗ` bases. -/
theorem spectralOrthonormalBasisMatrix_linear_twoNorm_le_paperSum
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ *
      deterministicDifferenceDistributionMatrix (fun a : State A n => L a) *
      spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ ≤
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        Real.sqrt ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
          ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
            (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
              (if k < n ∧ n < k + l₁ + l₂ then
                ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
                  (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
              else 0)) *
        Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let M := deterministicDifferenceDistributionMatrix (fun a : State A n => L a)
  calc
    ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
      spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ ≤
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ * M *
          spectralBasisMatrix (A := A) (n := n) l₂‖ *
        Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) :=
      spectralOrthonormalBasisMatrix_compression_twoNorm_le_gramBound
        l₁ l₂ u hu M
    _ ≤ _ := by
      gcongr
      exact spectralBasisMatrix_linear_twoNorm_le_paperSum
        L hMDS l₁ l₂ hpos hd

/-- The columns of the orthonormalized paper-style `Cₗ` span exactly `Wₗ`. -/
theorem spectralOrthonormalBasisMatrix_columnSpan_eq
    (l : ℕ) (u : A) (hu : u ≠ 0) :
    Submodule.span ℝ
      (Set.range (fun c : SpectralBasisIndex (A := A) (n := n) l =>
        fun a => spectralOrthonormalBasisMatrix (n := n) l u hu a c)) =
      spectralWeightSubspace (A := A) (n := n) l := by
  let B := spectralBasisMatrix (A := A) (n := n) l
  let R := spectralGramInverseSquareRoot (n := n) l u hu
  let C := spectralOrthonormalBasisMatrix (n := n) l u hu
  have hRunit : IsUnit R := by
    dsimp [R, spectralGramInverseSquareRoot]
    exact Matrix.isUnit_nonsing_inv_iff.mpr
      (spectralBasisMatrix_gram_posDef l u hu).posDef_sqrt.isUnit
  have hRsurj : Function.Surjective R.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hRunit
  have hrange : LinearMap.range C.mulVecLin = LinearMap.range B.mulVecLin := by
    rw [show C.mulVecLin = B.mulVecLin.comp R.mulVecLin by
      simpa only [C, B, R, spectralOrthonormalBasisMatrix] using
        Matrix.mulVecLin_mul B R]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨R *ᵥ y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hRsurj y
      exact ⟨z, by simp [LinearMap.comp_apply, hz]⟩
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin] at hrange
  change Submodule.span ℝ (Set.range C.col) = _
  rw [← spectralBasisColumnSubspace_eq_spectralWeightSubspace l]
  simpa [spectralBasisColumnSubspace, C, B, Matrix.col_apply] using hrange

/-- The paper's orthonormalized spectral columns preserve Euclidean coefficient norms. -/
theorem spectralOrthonormalBasisMatrix_mulVec_norm
    (l : ℕ) (u : A) (hu : u ≠ 0)
    (c : SpectralBasisIndex (A := A) (n := n) l → ℝ) :
    ‖WithLp.toLp 2
      ((spectralOrthonormalBasisMatrix (n := n) l u hu) *ᵥ c)‖ =
      ‖WithLp.toLp 2 c‖ := by
  let C := spectralOrthonormalBasisMatrix (n := n) l u hu
  have hdot : c ⬝ᵥ (Cᵀ *ᵥ (C *ᵥ c)) =
      (C *ᵥ c) ⬝ᵥ (C *ᵥ c) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hself : (C *ᵥ c) ⬝ᵥ (C *ᵥ c) = c ⬝ᵥ c := by
    calc
      (C *ᵥ c) ⬝ᵥ (C *ᵥ c) = c ⬝ᵥ (Cᵀ *ᵥ (C *ᵥ c)) := hdot.symm
      _ = c ⬝ᵥ ((Cᵀ * C) *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = c ⬝ᵥ c := by rw [spectralOrthonormalBasisMatrix_orthonormal l u hu,
        Matrix.one_mulVec]
  have hleft : ‖WithLp.toLp 2 (C *ᵥ c)‖ ^ 2 =
      (C *ᵥ c) ⬝ᵥ (C *ᵥ c) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, Real.norm_eq_abs, pow_two]
  have hright : ‖WithLp.toLp 2 c‖ ^ 2 = c ⬝ᵥ c := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, Real.norm_eq_abs, pow_two]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hleft, hright, hself]

/-- Every vector of `Wₗ` has coordinates in the paper's orthonormalized spectral matrix. -/
theorem spectralOrthonormalBasisMatrix_mulVec_surjective_onto_W
    (l : ℕ) (u : A) (hu : u ≠ 0)
    (v : State A n → ℝ)
    (hv : v ∈ spectralWeightSubspace (A := A) (n := n) l) :
    ∃ c : SpectralBasisIndex (A := A) (n := n) l → ℝ,
      spectralOrthonormalBasisMatrix (n := n) l u hu *ᵥ c = v := by
  let C := spectralOrthonormalBasisMatrix (n := n) l u hu
  have hrange : spectralWeightSubspace (A := A) (n := n) l =
      LinearMap.range C.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact (spectralOrthonormalBasisMatrix_columnSpan_eq l u hu).symm
  rw [hrange] at hv
  obtain ⟨c, hc⟩ := hv
  exact ⟨c, hc⟩

/-- Orthogonal projection onto `Wₗ` is `Cₗ Cₗᵀ` in the paper's orthonormal spectral coordinates. -/
theorem spectralWeight_orthogonalProjection_coordinates
    (l : ℕ) (u : A) (hu : u ≠ 0) (v : State A n → ℝ) :
    (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
      ((((spectralWeightHilbertSubspace (A := A) (n := n) l).orthogonalProjection
        (WithLp.toLp 2 v)) :
          spectralWeightHilbertSubspace (A := A) (n := n) l) :
            EuclideanSpace ℝ (State A n)) =
      spectralOrthonormalBasisMatrix (n := n) l u hu *ᵥ
        ((spectralOrthonormalBasisMatrix (n := n) l u hu)ᵀ *ᵥ v) := by
  let C := spectralOrthonormalBasisMatrix (n := n) l u hu
  let W := spectralWeightHilbertSubspace (A := A) (n := n) l
  let pHilbert := W.orthogonalProjection (WithLp.toLp 2 v)
  let p := (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
    (pHilbert : EuclideanSpace ℝ (State A n))
  have hp : p ∈ spectralWeightSubspace (A := A) (n := n) l :=
    (mem_spectralWeightHilbertSubspace_iff l
      (pHilbert : EuclideanSpace ℝ (State A n))).mp pHilbert.property
  obtain ⟨c, hc⟩ :=
    spectralOrthonormalBasisMatrix_mulVec_surjective_onto_W l u hu p hp
  have hc0 : C *ᵥ c = p := hc
  have hpair (z : SpectralBasisIndex (A := A) (n := n) l) :
      (C.col z) ⬝ᵥ p = (C.col z) ⬝ᵥ v := by
    have hz' : C.col z ∈ spectralWeightSubspace (A := A) (n := n) l := by
      rw [← spectralOrthonormalBasisMatrix_columnSpan_eq l u hu]
      exact Submodule.subset_span ⟨z, rfl⟩
    have hz : (WithLp.toLp 2 (C.col z) : EuclideanSpace ℝ (State A n)) ∈ W := by
      rw [mem_spectralWeightHilbertSubspace_iff]
      exact hz'
    let cz : W := ⟨WithLp.toLp 2 (C.col z), hz⟩
    have hi := W.inner_orthogonalProjection_eq_of_mem_left cz (WithLp.toLp 2 v)
    rw [Submodule.coe_inner] at hi
    rw [euclidean_inner_eq_dotProduct, euclidean_inner_eq_dotProduct] at hi
    change (C.col z) ⬝ᵥ p = (C.col z) ⬝ᵥ v at hi
    exact hi
  have hnormal : Cᵀ *ᵥ p = Cᵀ *ᵥ v := by
    funext z
    change (C.col z) ⬝ᵥ p = (C.col z) ⬝ᵥ v
    exact hpair z
  have hcoord : c = Cᵀ *ᵥ v := by
    calc
      c = (Cᵀ * C) *ᵥ c := by
        rw [spectralOrthonormalBasisMatrix_orthonormal l u hu,
          Matrix.one_mulVec]
      _ = Cᵀ *ᵥ (C *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = Cᵀ *ᵥ p := by rw [hc0]
      _ = Cᵀ *ᵥ v := hnormal
  change p = C *ᵥ (Cᵀ *ᵥ v)
  rw [← hcoord]
  exact hc0.symm

/-- The actual projected operator `π_{Wₗ₁} M i_{Wₗ₂}` between the paper's spectral-weight subspaces. -/
noncomputable def spectralWeightBlockOperator
    (l₁ l₂ : ℕ) (M : Matrix (State A n) (State A n) ℝ) :
    spectralWeightHilbertSubspace (A := A) (n := n) l₂ →L[ℝ]
      spectralWeightHilbertSubspace (A := A) (n := n) l₁ :=
  (spectralWeightHilbertSubspace (A := A) (n := n) l₁).orthogonalProjection ∘L
    (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M) ∘L
      (spectralWeightHilbertSubspace (A := A) (n := n) l₂).subtypeL

/-- Its operator norm is bounded by the norm of `Cₗ₁ᵀ M Cₗ₂`, the matrix in the paper's orthonormal spectral coordinates. -/
theorem spectralWeightBlockOperator_norm_le_compression
    (l₁ l₂ : ℕ) (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂ M‖ ≤
      ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
        spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ := by
  let C₁ := spectralOrthonormalBasisMatrix (n := n) l₁ u hu
  let C₂ := spectralOrthonormalBasisMatrix (n := n) l₂ u hu
  let K := C₁ᵀ * M * C₂
  let W₁ := spectralWeightHilbertSubspace (A := A) (n := n) l₁
  let W₂ := spectralWeightHilbertSubspace (A := A) (n := n) l₂
  let T := spectralWeightBlockOperator (n := n) l₁ l₂ M
  change ‖T‖ ≤ ‖K‖
  apply T.opNorm_le_bound (norm_nonneg K)
  intro v
  obtain ⟨c, hc⟩ :=
    spectralOrthonormalBasisMatrix_mulVec_surjective_onto_W l₂ u hu
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ))
        (v : EuclideanSpace ℝ (State A n)))
      ((mem_spectralWeightHilbertSubspace_iff l₂
        (v : EuclideanSpace ℝ (State A n))).mp v.property)
  have hv : (v : EuclideanSpace ℝ (State A n)) =
      WithLp.toLp 2 (C₂ *ᵥ c) := by
    apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
    simpa only [WithLp.linearEquiv_apply] using hc.symm
  have hp :
      (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
        ((T v : W₁) : EuclideanSpace ℝ (State A n)) =
      C₁ *ᵥ (K *ᵥ c) := by
    change (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
      (((W₁.orthogonalProjection
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
          (v : EuclideanSpace ℝ (State A n)))) : W₁) :
          EuclideanSpace ℝ (State A n)) = _
    rw [hv, Matrix.toEuclideanCLM_toLp]
    rw [spectralWeight_orthogonalProjection_coordinates l₁ u hu]
    simp only [Matrix.mulVec_mulVec, K, C₁, C₂, Matrix.mul_assoc]
  have hTv : ‖T v‖ = ‖WithLp.toLp 2 (C₁ *ᵥ (K *ᵥ c))‖ := by
    change ‖((T v : W₁) : EuclideanSpace ℝ (State A n))‖ = _
    apply congrArg norm
    apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
    simpa only [WithLp.linearEquiv_apply] using hp
  have hvnorm : ‖v‖ = ‖WithLp.toLp 2 c‖ := by
    change ‖(v : EuclideanSpace ℝ (State A n))‖ = _
    rw [hv]
    exact spectralOrthonormalBasisMatrix_mulVec_norm l₂ u hu c
  rw [hTv, hvnorm, spectralOrthonormalBasisMatrix_mulVec_norm l₁ u hu]
  exact Matrix.l2_opNorm_mulVec K (WithLp.toLp 2 c)

/-- The paper's spectral MDS sum bounds the actual projected linear-layer operator between `Wₗ` spaces. -/
theorem spectralWeightBlockOperator_linear_twoNorm_le_paperSum
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ≤
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        Real.sqrt ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
          ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
            (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
              (if k < n ∧ n < k + l₁ + l₂ then
                ((Fintype.card A : ℝ)⁻¹) ^ (2 * n - k - (l₁ + l₂)) *
                  (2 ^ (n - k) * ((Fintype.card A : ℝ) - 1) ^ (n - k))
              else 0)) *
        Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let M := deterministicDifferenceDistributionMatrix
    (fun a : State A n => L a)
  exact (spectralWeightBlockOperator_norm_le_compression l₁ l₂ u hu M).trans
    (spectralOrthonormalBasisMatrix_linear_twoNorm_le_paperSum
      u hu L hMDS l₁ l₂ hpos hd)

/-- Reindex the paper's admissible zero-coordinate count by `i = n-k`. The restriction `l ≤ n` is the range used when this estimate feeds Theorem 3. -/
theorem spectralPaperRange_reindex
    (n l : ℕ) (hl : l ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (2 * n - l + 1),
      if k < n ∧ n < k + l then f k else 0) =
      ∑ i ∈ Finset.Icc 1 (l - 1), f (n - i) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij'
    (fun k _ => n - k) (fun i _ => n - i)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro k hk
    congr 1
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega

/-- The paper's exact Frobenius sum after `i = n-k`, before replacing `q-1` by `q`. -/
theorem spectralPaperFrobeniusSum_reindex
    (q : ℝ) (n l : ℕ) (hl : l ≤ n) :
    (∑ k ∈ Finset.range (2 * n - l + 1),
      (Nat.choose (2 * n - l) k : ℝ) *
        (if k < n ∧ n < k + l then
          q⁻¹ ^ (2 * n - k - l) *
            (2 ^ (n - k) * (q - 1) ^ (n - k))
        else 0)) =
      ∑ i ∈ Finset.Icc 1 (l - 1),
        (Nat.choose (2 * n - l) (n - i) : ℝ) *
          (q⁻¹ ^ (n + i - l) *
            (2 ^ i * (q - 1) ^ i)) := by
  classical
  simp_rw [mul_ite, mul_zero]
  calc
    (∑ k ∈ Finset.range (2 * n - l + 1),
      if k < n ∧ n < k + l then
        (Nat.choose (2 * n - l) k : ℝ) *
          (q⁻¹ ^ (2 * n - k - l) *
            (2 ^ (n - k) * (q - 1) ^ (n - k))) else 0) =
      ∑ i ∈ Finset.Icc 1 (l - 1),
        (Nat.choose (2 * n - l) (n - i) : ℝ) *
          (q⁻¹ ^ (2 * n - (n - i) - l) *
            (2 ^ (n - (n - i)) * (q - 1) ^ (n - (n - i)))) :=
      spectralPaperRange_reindex n l hl _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have h1 : n - (n - i) = i := by omega
      have h2 : 2 * n - (n - i) - l = n + i - l := by omega
      rw [h1, h2]

/-- The paper's estimate `(q-1)^i/q^(n+i-l) ≤ q^(-(n-l))`. -/
theorem spectralPowerTerm_le
    (q : ℝ) (n l i : ℕ) (hq : 1 ≤ q) (hl : l ≤ n) :
    q⁻¹ ^ (n + i - l) * (q - 1) ^ i ≤ q⁻¹ ^ (n - l) := by
  have hqpos : 0 < q := by linarith
  have hinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  have hbase0 : 0 ≤ q⁻¹ * (q - 1) :=
    mul_nonneg hinv (sub_nonneg.mpr hq)
  have hbase1 : q⁻¹ * (q - 1) ≤ 1 := by
    calc
      q⁻¹ * (q - 1) ≤ q⁻¹ * q :=
        mul_le_mul_of_nonneg_left (by linarith) hinv
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hqpos)
  have hpow : (q⁻¹ * (q - 1)) ^ i ≤ 1 := by
    exact (pow_le_pow_left₀ hbase0 hbase1 i).trans_eq (one_pow i)
  have he : n + i - l = (n - l) + i := by omega
  calc
    q⁻¹ ^ (n + i - l) * (q - 1) ^ i =
      q⁻¹ ^ (n - l) * (q⁻¹ * (q - 1)) ^ i := by
        rw [he, pow_add, mul_pow]
        ring
    _ ≤ q⁻¹ ^ (n - l) * 1 :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hinv _)
    _ = q⁻¹ ^ (n - l) := mul_one _

/-- The paper's Frobenius sum is bounded by `q^(-(n-l))` times its binomial sum, in the Theorem 3 range `l ≤ n`. -/
theorem spectralPaperFrobeniusSum_le
    (q : ℝ) (n l : ℕ) (hq : 1 ≤ q) (hl : l ≤ n) :
    (∑ k ∈ Finset.range (2 * n - l + 1),
      (Nat.choose (2 * n - l) k : ℝ) *
        (if k < n ∧ n < k + l then
          q⁻¹ ^ (2 * n - k - l) *
            (2 ^ (n - k) * (q - 1) ^ (n - k))
        else 0)) ≤
      q⁻¹ ^ (n - l) *
        ∑ i ∈ Finset.Icc 1 (l - 1),
          (Nat.choose (2 * n - l) (n - i) : ℝ) * 2 ^ i := by
  rw [spectralPaperFrobeniusSum_reindex q n l hl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := spectralPowerTerm_le q n l i hq hl
  calc
    (Nat.choose (2 * n - l) (n - i) : ℝ) *
        (q⁻¹ ^ (n + i - l) * (2 ^ i * (q - 1) ^ i)) =
      ((Nat.choose (2 * n - l) (n - i) : ℝ) * 2 ^ i) *
        (q⁻¹ ^ (n + i - l) * (q - 1) ^ i) := by ring
    _ ≤ ((Nat.choose (2 * n - l) (n - i) : ℝ) * 2 ^ i) *
        q⁻¹ ^ (n - l) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = q⁻¹ ^ (n - l) *
        ((Nat.choose (2 * n - l) (n - i) : ℝ) * 2 ^ i) := by ring

private theorem spectral_sqrt_triprod_sq_le
    (x a b c d e : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : d ≤ e)
    (h : x ≤ Real.sqrt a * Real.sqrt (b * d) * Real.sqrt c) :
    x ^ 2 ≤ a * (b * e) * c := by
  have hbd : 0 ≤ b * d := mul_nonneg hb hd
  have hroot : 0 ≤ Real.sqrt a * Real.sqrt (b * d) * Real.sqrt c := by
    positivity
  have hsq := (sq_le_sq₀ hx hroot).mpr h
  have hmult : a * (b * d) * c ≤ a * (b * e) * c := by
    gcongr
  calc
    x ^ 2 ≤ (Real.sqrt a * Real.sqrt (b * d) * Real.sqrt c) ^ 2 := hsq
    _ = a * (b * d) * c := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ha,
        Real.sq_sqrt hbd, Real.sq_sqrt hc]
    _ ≤ a * (b * e) * c := hmult

/-- The squared projected linear-layer block obeys the paper's reindexed Frobenius estimate, with both exact Gram losses. -/
theorem spectralWeightBlockOperator_linear_sq_le_reindexed
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hl : l₁ + l₂ ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤
      ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹ *
        ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
          (((Fintype.card A : ℝ)⁻¹) ^ (n - (l₁ + l₂)) *
            ∑ i ∈ Finset.Icc 1 (l₁ + l₂ - 1),
              (Nat.choose (2 * n - (l₁ + l₂)) (n - i) : ℝ) * 2 ^ i)) *
        ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹ := by
  let q : ℝ := Fintype.card A
  let a : ℝ := ((1 - (Real.sqrt q)⁻¹) ^ (n - l₁))⁻¹
  let c : ℝ := ((1 - (Real.sqrt q)⁻¹) ^ (n - l₂))⁻¹
  let b : ℝ := (Nat.choose n l₁ * Nat.choose n l₂ : ℕ)
  let d : ℝ := ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
      (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) *
        (if k < n ∧ n < k + l₁ + l₂ then
          q⁻¹ ^ (2 * n - k - (l₁ + l₂)) *
            (2 ^ (n - k) * (q - 1) ^ (n - k))
        else 0)
  let e : ℝ := q⁻¹ ^ (n - (l₁ + l₂)) *
    ∑ i ∈ Finset.Icc 1 (l₁ + l₂ - 1),
      (Nat.choose (2 * n - (l₁ + l₂)) (n - i) : ℝ) * 2 ^ i
  have hqreal : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 1 ≤ Fintype.card A by omega)
  have ha : 0 ≤ a := by
    have hnorm := spectralBasisMatrix_gram_inverse_twoNorm_le (n := n) l₁ u hu
    exact (norm_nonneg _).trans hnorm
  have hc : 0 ≤ c := by
    have hnorm := spectralBasisMatrix_gram_inverse_twoNorm_le (n := n) l₂ u hu
    exact (norm_nonneg _).trans hnorm
  have hb : 0 ≤ b := by positivity
  have hqminus : 0 ≤ q - 1 := sub_nonneg.mpr hqreal
  have hqinverse : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith : 0 ≤ q)
  have hd : 0 ≤ d := by
    dsimp [d]
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) <|
        mul_nonneg (pow_nonneg hqinverse _) <|
          mul_nonneg (by positivity) (pow_nonneg hqminus _)
    · simp
  have hde : d ≤ e := by
    dsimp [d, e]
    simpa only [Nat.add_assoc] using
      (spectralPaperFrobeniusSum_le q n (l₁ + l₂) hqreal hl)
  have hroot :
      ‖spectralWeightBlockOperator (n := n) l₁ l₂
        (deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a))‖ ≤
        Real.sqrt a * Real.sqrt (b * d) * Real.sqrt c := by
    exact spectralWeightBlockOperator_linear_twoNorm_le_paperSum
      u hu L hMDS l₁ l₂ hpos
        (wordActivityOrthogonal_finrank_pos_of_card_ge_three hq)
  exact spectral_sqrt_triprod_sq_le _ a b c d e
    (norm_nonneg (spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix (fun a : State A n => L a))))
    ha hb hc hd hde hroot

private theorem spectral_power_rearrange (a b : ℝ) (m i j : ℕ) :
    a ^ (m + j) * b ^ m * a ^ (m + i) =
      a ^ (i + j) * (a ^ 2 * b) ^ m := by
  have hpow : (a ^ 2) ^ m = (a ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
  rw [pow_add, pow_add, mul_pow, hpow, pow_add]
  ring

/-- Algebraic identity combining the two Gram losses with the paper's `q^(-(n-l))` factor. -/
theorem spectralGramPower_identity
    (q : ℝ) (n l₁ l₂ : ℕ) (hq : 1 < q) (hl : l₁ + l₂ ≤ n) :
    ((1 - (Real.sqrt q)⁻¹) ^ (n - l₁))⁻¹ *
      q⁻¹ ^ (n - (l₁ + l₂)) *
      ((1 - (Real.sqrt q)⁻¹) ^ (n - l₂))⁻¹ =
      (1 + (Real.sqrt q - 1)⁻¹) ^ (l₁ + l₂) *
        (Real.sqrt q - 1)⁻¹ ^ (2 * (n - (l₁ + l₂))) := by
  let s : ℝ := Real.sqrt q
  let a : ℝ := (1 - s⁻¹)⁻¹
  let d : ℝ := (s - 1)⁻¹
  let m : ℕ := n - (l₁ + l₂)
  have hs : 1 < s := by
    dsimp [s]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hs0 : s ≠ 0 := ne_of_gt (by linarith)
  have ht0 : s - 1 ≠ 0 := ne_of_gt (by linarith)
  have hqeq : q = s ^ 2 := by
    dsimp [s]
    exact (Real.sq_sqrt (by linarith : 0 ≤ q)).symm
  have ha : a = 1 + d := by
    dsimp [a, d]
    field_simp [hs0, ht0]
  have hbase : a ^ 2 * q⁻¹ = d ^ 2 := by
    rw [hqeq]
    dsimp [a, d]
    field_simp [hs0, ht0]
    ring
  have h1 : n - l₁ = m + l₂ := by dsimp [m]; omega
  have h2 : n - l₂ = m + l₁ := by dsimp [m]; omega
  change ((1 - s⁻¹) ^ (n - l₁))⁻¹ * q⁻¹ ^ m *
      ((1 - s⁻¹) ^ (n - l₂))⁻¹ = (1 + d) ^ (l₁ + l₂) * d ^ (2 * m)
  rw [← inv_pow, ← inv_pow]
  change a ^ (n - l₁) * q⁻¹ ^ m * a ^ (n - l₂) = _
  rw [h1, h2, spectral_power_rearrange, hbase, ha]
  ring

/-- The combined Gram and alphabet factors equal the exact coefficient displayed in the paper. -/
theorem spectralGramPower_paperForm
    (q : ℝ) (n l₁ l₂ : ℕ) (hq : 1 < q) (hl : l₁ + l₂ ≤ n) :
    ((1 - (Real.sqrt q)⁻¹) ^ (n - l₁))⁻¹ *
      q⁻¹ ^ (n - (l₁ + l₂)) *
      ((1 - (Real.sqrt q)⁻¹) ^ (n - l₂))⁻¹ =
      (1 + 1 / (Real.sqrt q - 1)) ^ (l₁ + l₂) /
        (Real.sqrt q - 1) ^ (2 * n - 2 * (l₁ + l₂)) := by
  rw [spectralGramPower_identity q n l₁ l₂ hq hl]
  have he : 2 * (n - (l₁ + l₂)) = 2 * n - 2 * (l₁ + l₂) := by omega
  rw [he]
  simp only [inv_pow, div_eq_mul_inv, one_mul]

/-- The paper's spectral Frobenius lemma for the range `l₁+l₂ ≤ n` used in Theorem 3: the actual projected linear-layer block has the displayed `C(n,l₁,l₂)` bound. -/
theorem spectralFrobeniusBound_paper
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hl : l₁ + l₂ ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤
      ((1 + 1 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ (l₁ + l₂) *
        (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
        ∑ i ∈ Finset.Icc 1 (l₁ + l₂ - 1),
          (Nat.choose (2 * n - (l₁ + l₂)) (n - i) : ℝ) * 2 ^ i) /
        (Real.sqrt (Fintype.card A : ℝ) - 1) ^
          (2 * n - 2 * (l₁ + l₂)) := by
  let q : ℝ := Fintype.card A
  let a : ℝ := ((1 - (Real.sqrt q)⁻¹) ^ (n - l₁))⁻¹
  let c : ℝ := ((1 - (Real.sqrt q)⁻¹) ^ (n - l₂))⁻¹
  let b : ℝ := (Nat.choose n l₁ * Nat.choose n l₂ : ℕ)
  let S : ℝ := ∑ i ∈ Finset.Icc 1 (l₁ + l₂ - 1),
    (Nat.choose (2 * n - (l₁ + l₂)) (n - i) : ℝ) * 2 ^ i
  have hqreal : 1 < q := by
    dsimp [q]
    exact_mod_cast (show 1 < Fintype.card A by omega)
  have hgram : a * q⁻¹ ^ (n - (l₁ + l₂)) * c =
      (1 + 1 / (Real.sqrt q - 1)) ^ (l₁ + l₂) /
        (Real.sqrt q - 1) ^ (2 * n - 2 * (l₁ + l₂)) :=
    spectralGramPower_paperForm q n l₁ l₂ hqreal hl
  calc
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤
      a * (b * (q⁻¹ ^ (n - (l₁ + l₂)) * S)) * c :=
        spectralWeightBlockOperator_linear_sq_le_reindexed
          u hu L hMDS l₁ l₂ hpos hl hq
    _ = (a * q⁻¹ ^ (n - (l₁ + l₂)) * c) * (b * S) := by ring
    _ = ((1 + 1 / (Real.sqrt q - 1)) ^ (l₁ + l₂) /
        (Real.sqrt q - 1) ^ (2 * n - 2 * (l₁ + l₂))) * (b * S) := by
          rw [hgram]
    _ = _ := by
      dsimp [q, b, S]
      ring

/-- If the adjoint preserves a closed subspace, the projection of the output depends only on the projection of the input. -/
theorem projection_after_adjoint_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (T : E →L[ℝ] E)
    (h : ∀ u ∈ U, T.adjoint u ∈ U) (y : E) :
    U.orthogonalProjection (T y) =
      U.orthogonalProjection (T (U.starProjection y)) := by
  let r := y - U.starProjection y
  have hr : r ∈ Uᗮ := U.sub_starProjection_mem_orthogonal y
  have hTr : T r ∈ Uᗮ := by
    apply (U.mem_orthogonal' (T r)).2
    intro u hu
    rw [← T.adjoint_inner_right]
    exact (U.mem_orthogonal' r).1 hr _ (h u hu)
  have hz : U.orthogonalProjection (T r) = 0 :=
    U.orthogonalProjection_eq_zero_iff.mpr hTr
  calc
    U.orthogonalProjection (T y) =
      U.orthogonalProjection (T (U.starProjection y + r)) := by
        have hy : y = U.starProjection y + r := by
          dsimp [r]
          abel
        exact congrArg (fun z => U.orthogonalProjection (T z)) hy
    _ = U.orthogonalProjection (T (U.starProjection y)) := by
      simp [map_add, hz]

/-- Pythagoras for the paper’s decomposition `V⊥ = W₁ ⊕ ⋯ ⊕ Wₙ`: projection onto the complement has squared norm equal to the sum of its spectral-weight projections. -/
theorem activityOrthogonal_projection_norm_sq_eq_sum_spectralWeight
    (y : EuclideanSpace ℝ (State A n)) :
    ‖(activityHilbertSubspace (A := A) (n := n))ᗮ.orthogonalProjection y‖ ^ 2 =
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 n},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection y‖ ^ 2 := by
  classical
  let E := EuclideanSpace ℝ (State A n)
  let Q := (activityHilbertSubspace (A := A) (n := n))ᗮ
  let J := Finset.Icc 1 n
  let U (i : {i : ℕ // i ∈ J}) :=
    spectralWeightHilbertSubspace (A := A) (n := n) i.1
  let x : E := Q.starProjection y
  have horth : OrthogonalFamily ℝ (fun i => U i)
      (fun i => (U i).subtypeₗᵢ) := by
    intro i j hij a b
    have hweights : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply spectralWeightSubspaces_euclidean_orthogonal i.1 j.1 hweights
    · exact (mem_spectralWeightHilbertSubspace_iff i.1 _).mp a.property
    · exact (mem_spectralWeightHilbertSubspace_iff j.1 _).mp b.property
  have hx : x ∈ ⨆ i, U i := by
    change x ∈ spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J
    rw [spectralWeightIndexSet_Icc_one_eq_activityOrthogonal]
    exact Q.starProjection_apply_mem y
  have hsum : (∑ i, ((U i).orthogonalProjection x : E)) = x := by
    simpa only [Submodule.starProjection_apply] using
      horth.sum_projection_of_mem_iSup x hx
  have hnorm := horth.norm_sum (fun i => (U i).orthogonalProjection x) Finset.univ
  change ‖∑ i, ((U i).orthogonalProjection x : E)‖ ^ 2 =
    ∑ i, ‖(U i).orthogonalProjection x‖ ^ 2 at hnorm
  rw [hsum] at hnorm
  have hproj (i : {i : ℕ // i ∈ J}) :
      (U i).orthogonalProjection x = (U i).orthogonalProjection y := by
    have hle : U i ≤ Q := by
      change spectralWeightHilbertSubspace (A := A) (n := n) i.1 ≤
        (activityHilbertSubspace (A := A) (n := n))ᗮ
      rw [← spectralWeightIndexSet_Icc_one_eq_activityOrthogonal]
      exact le_iSup (fun i => U i) i
    exact Submodule.orthogonalProjection_starProjection_of_le hle y
  change ‖x‖ ^ 2 = ∑ i, ‖(U i).orthogonalProjection y‖ ^ 2
  rw [hnorm]
  simp_rw [hproj]

/-- The mixed block from the paper’s activity space to its high-weight tail. -/
noncomputable def activityToHighWeightOperator
    (l : ℕ) (M : Matrix (State A n) (State A n) ℝ) :
    activityHilbertSubspace (A := A) (n := n) →L[ℝ]
      spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n) :=
  (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
    (Finset.Icc (l + 1) n)).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
      (activityHilbertSubspace (A := A) (n := n)).subtypeL

/-- Pythagoras for any finite set of the paper's mutually orthogonal `W_l` spaces. -/
theorem spectralWeightIndexSet_projection_norm_sq_eq_sum
    (J : Finset ℕ) (y : EuclideanSpace ℝ (State A n)) :
    ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J).orthogonalProjection y‖ ^ 2 =
      ∑ i : {i : ℕ // i ∈ J},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection y‖ ^ 2 := by
  classical
  let E := EuclideanSpace ℝ (State A n)
  let Q := spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J
  let U (i : {i : ℕ // i ∈ J}) :=
    spectralWeightHilbertSubspace (A := A) (n := n) i.1
  let x : E := Q.starProjection y
  have horth : OrthogonalFamily ℝ (fun i => U i)
      (fun i => (U i).subtypeₗᵢ) := by
    intro i j hij a b
    have hweights : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply spectralWeightSubspaces_euclidean_orthogonal i.1 j.1 hweights
    · exact (mem_spectralWeightHilbertSubspace_iff i.1 _).mp a.property
    · exact (mem_spectralWeightHilbertSubspace_iff j.1 _).mp b.property
  have hx : x ∈ ⨆ i, U i := Q.starProjection_apply_mem y
  have hsum : (∑ i, ((U i).orthogonalProjection x : E)) = x := by
    simpa only [Submodule.starProjection_apply] using
      horth.sum_projection_of_mem_iSup x hx
  have hnorm := horth.norm_sum (fun i => (U i).orthogonalProjection x) Finset.univ
  change ‖∑ i, ((U i).orthogonalProjection x : E)‖ ^ 2 =
    ∑ i, ‖(U i).orthogonalProjection x‖ ^ 2 at hnorm
  rw [hsum] at hnorm
  have hproj (i : {i : ℕ // i ∈ J}) :
      (U i).orthogonalProjection x = (U i).orthogonalProjection y := by
    have hle : U i ≤ Q := le_iSup (fun i => U i) i
    exact Submodule.orthogonalProjection_starProjection_of_le hle y
  change ‖x‖ ^ 2 = ∑ i, ‖(U i).orthogonalProjection y‖ ^ 2
  rw [hnorm]
  simp_rw [hproj]

/-- Split a finite subtype-indexed interval sum at an integer cutoff. -/
theorem finiteIntervalSubtypeSum_split (f : ℕ → ℝ) (l n : ℕ) (hl : l ≤ n) :
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 n}, f i.1) =
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l}, f i.1) +
      (∑ i : {i : ℕ // i ∈ Finset.Icc (l + 1) n}, f i.1) := by
  classical
  have hdis : Disjoint (Finset.Icc 1 l) (Finset.Icc (l + 1) n) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    omega
  have hunion : Finset.Icc 1 l ∪ Finset.Icc (l + 1) n = Finset.Icc 1 n := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hsum : (∑ i ∈ Finset.Icc 1 n, f i) =
      (∑ i ∈ Finset.Icc 1 l, f i) +
        (∑ i ∈ Finset.Icc (l + 1) n, f i) := by
    rw [← hunion, Finset.sum_union hdis]
  change (∑ i ∈ (Finset.Icc 1 n).attach, f i.1) =
    (∑ i ∈ (Finset.Icc 1 l).attach, f i.1) +
      (∑ i ∈ (Finset.Icc (l + 1) n).attach, f i.1)
  simpa only [Finset.sum_attach] using hsum

/-- The paper’s decomposition of the squared `V⊥` projection into weights through `l` and the `W_{>l}` tail. -/
theorem activityOrthogonal_projection_norm_sq_eq_low_add_tail
    (l : ℕ) (hl : l ≤ n) (y : EuclideanSpace ℝ (State A n)) :
    ‖(activityHilbertSubspace (A := A) (n := n))ᗮ.orthogonalProjection y‖ ^ 2 =
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection y‖ ^ 2) +
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n)).orthogonalProjection y‖ ^ 2 := by
  let f (i : ℕ) : ℝ :=
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) i).orthogonalProjection y‖ ^ 2
  have hfull := activityOrthogonal_projection_norm_sq_eq_sum_spectralWeight
    (A := A) (n := n) y
  have htail := spectralWeightIndexSet_projection_norm_sq_eq_sum
    (A := A) (n := n) (Finset.Icc (l + 1) n) y
  have hsplit := finiteIntervalSubtypeSum_split f l n hl
  calc
    ‖(activityHilbertSubspace (A := A) (n := n))ᗮ.orthogonalProjection y‖ ^ 2 =
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 n}, f i.1 := hfull
    _ = (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l}, f i.1) +
        (∑ i : {i : ℕ // i ∈ Finset.Icc (l + 1) n}, f i.1) := hsplit
    _ = _ := by rw [htail]

set_option maxHeartbeats 800000 in
/-- The mixed operator norm splits into the finite `W₁,…,Wₗ` squared block norms and one high-weight tail norm. -/
theorem activityToComplementOperator_norm_sq_le_low_add_tail
    (l : ℕ) (hl : l ≤ n)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖activityToComplementOperator M‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
          (activityHilbertSubspace (A := A) (n := n)).subtypeL‖ ^ 2) +
      ‖activityToHighWeightOperator (n := n) l M‖ ^ 2 := by
  classical
  let K := activityHilbertSubspace (A := A) (n := n)
  let F := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
  let T := activityToComplementOperator M
  let U (i : {i : ℕ // i ∈ Finset.Icc 1 l}) :=
    spectralWeightHilbertSubspace (A := A) (n := n) i.1
  let B (i : {i : ℕ // i ∈ Finset.Icc 1 l}) : K →L[ℝ] U i :=
    (U i).orthogonalProjection ∘L F ∘L K.subtypeL
  let R := activityToHighWeightOperator (A := A) (n := n) l M
  let C : ℝ := (∑ i, ‖B i‖ ^ 2) + ‖R‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (x : K) : ‖T x‖ ^ 2 = (∑ i, ‖B i x‖ ^ 2) + ‖R x‖ ^ 2 := by
    have h := activityOrthogonal_projection_norm_sq_eq_low_add_tail
      (A := A) (n := n) l hl (F (x : EuclideanSpace ℝ (State A n)))
    simpa only [T, R, B, U, F, K, activityToComplementOperator,
      activityToHighWeightOperator, ContinuousLinearMap.comp_apply,
      Submodule.coe_norm] using h
  have hsum (x : K) :
      (∑ i, ‖B i x‖ ^ 2) + ‖R x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
    have hlow : (∑ i, ‖B i x‖ ^ 2) ≤ ∑ i, (‖B i‖ * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        ((B i).le_opNorm x)
    have htail : ‖R x‖ ^ 2 ≤ (‖R‖ * ‖x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (R.le_opNorm x)
    calc
      _ ≤ (∑ i, (‖B i‖ * ‖x‖) ^ 2) + (‖R‖ * ‖x‖) ^ 2 :=
        add_le_add hlow htail
      _ = C * ‖x‖ ^ 2 := by
        simp only [mul_pow, C, Finset.sum_mul, add_mul]
  have hbound : ‖T‖ ≤ Real.sqrt C := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg C)
    intro x
    have hs := (hpoint x).le.trans (hsum x)
    have hsq : ‖T x‖ ^ 2 ≤ (Real.sqrt C * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC]
      exact hs
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 hsq
  have hsq := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg C)).2 hbound
  change ‖T‖ ^ 2 ≤ C
  simpa only [Real.sq_sqrt hC] using hsq

/-- The operator between two unions of spectral-weight spaces. -/
noncomputable def spectralWeightIndexSetBlockOperator
    (Jout Jin : Finset ℕ) (M : Matrix (State A n) (State A n) ℝ) :
    spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jin →L[ℝ]
      spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jout :=
  (spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jout).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
      (spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jin).subtypeL

set_option maxHeartbeats 800000 in
/-- Pythagoras gives a squared operator-norm bound for arbitrary source subspaces. -/
theorem activityOrthogonalOperator_norm_sq_le_low_add_tail
    (U : Submodule ℝ (EuclideanSpace ℝ (State A n)))
    (F : U →L[ℝ] EuclideanSpace ℝ (State A n))
    (l : ℕ) (hl : l ≤ n) :
    ‖(activityHilbertSubspace (A := A) (n := n))ᗮ.orthogonalProjection ∘L F‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L F‖ ^ 2) +
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n)).orthogonalProjection ∘L F‖ ^ 2 := by
  classical
  let Q := (activityHilbertSubspace (A := A) (n := n))ᗮ
  let T : U →L[ℝ] Q := Q.orthogonalProjection ∘L F
  let W (i : {i : ℕ // i ∈ Finset.Icc 1 l}) :=
    spectralWeightHilbertSubspace (A := A) (n := n) i.1
  let B (i : {i : ℕ // i ∈ Finset.Icc 1 l}) : U →L[ℝ] W i :=
    (W i).orthogonalProjection ∘L F
  let R : U →L[ℝ] spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
      (Finset.Icc (l + 1) n) :=
    (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
      (Finset.Icc (l + 1) n)).orthogonalProjection ∘L F
  let C : ℝ := (∑ i, ‖B i‖ ^ 2) + ‖R‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (x : U) : ‖T x‖ ^ 2 = (∑ i, ‖B i x‖ ^ 2) + ‖R x‖ ^ 2 := by
    have h := activityOrthogonal_projection_norm_sq_eq_low_add_tail
      (A := A) (n := n) l hl (F x)
    simpa only [T, R, B, W, Q, ContinuousLinearMap.comp_apply,
      Submodule.coe_norm] using h
  have hsum (x : U) :
      (∑ i, ‖B i x‖ ^ 2) + ‖R x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
    have hlow : (∑ i, ‖B i x‖ ^ 2) ≤ ∑ i, (‖B i‖ * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        ((B i).le_opNorm x)
    have htail : ‖R x‖ ^ 2 ≤ (‖R‖ * ‖x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (R.le_opNorm x)
    calc
      _ ≤ (∑ i, (‖B i‖ * ‖x‖) ^ 2) + (‖R‖ * ‖x‖) ^ 2 :=
        add_le_add hlow htail
      _ = C * ‖x‖ ^ 2 := by
        simp only [mul_pow, C, Finset.sum_mul, add_mul]
  have hbound : ‖T‖ ≤ Real.sqrt C := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg C)
    intro x
    have hs := (hpoint x).le.trans (hsum x)
    have hsq : ‖T x‖ ^ 2 ≤ (Real.sqrt C * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC]
      exact hs
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 hsq
  have hsq := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg C)).2 hbound
  change ‖T‖ ^ 2 ≤ C
  simpa only [Real.sq_sqrt hC] using hsq

theorem spectralWeightIndexSet_singleton_eq (i : ℕ) :
    spectralWeightIndexSetHilbertSubspace (A := A) (n := n) {i} =
      spectralWeightHilbertSubspace (A := A) (n := n) i := by
  unfold spectralWeightIndexSetHilbertSubspace
  simp

/-- The first, output-side split in the paper's `V⊥ → V⊥` argument. -/
theorem activityComplementOperator_norm_sq_le_outputLowTail
    (M : Matrix (State A n) (State A n) ℝ)
    (l : ℕ) (hl : l ≤ n) :
    ‖activityComplementOperator M‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
          ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2) +
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n)).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
          ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2 := by
  let Q := (activityHilbertSubspace (A := A) (n := n))ᗮ
  let F : Q →L[ℝ] EuclideanSpace ℝ (State A n) :=
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L Q.subtypeL
  simpa only [activityComplementOperator, Q, F, ContinuousLinearMap.comp_assoc] using
    activityOrthogonalOperator_norm_sq_le_low_add_tail (A := A) (n := n) Q F l hl

omit [AddCommGroup A] [DecidableEq A] in
/-- The Hilbert adjoint of a projected block swaps its input and output spaces. -/
theorem spectralProjectedBlock_adjoint
    (U V : Submodule ℝ (EuclideanSpace ℝ (State A n)))
    (F : EuclideanSpace ℝ (State A n) →L[ℝ] EuclideanSpace ℝ (State A n)) :
    ContinuousLinearMap.adjoint (V.orthogonalProjection ∘L F ∘L U.subtypeL) =
      U.orthogonalProjection ∘L (ContinuousLinearMap.adjoint F) ∘L V.subtypeL := by
  simp only [ContinuousLinearMap.adjoint_comp,
    U.adjoint_subtypeL, V.adjoint_orthogonalProjection]
  ext x
  rfl

set_option maxHeartbeats 800000 in
/-- The input-side split in the paper's `V⊥ → Wᵢ` estimate. -/
theorem spectralRow_norm_sq_le_inputLowTail
    (W : Submodule ℝ (EuclideanSpace ℝ (State A n)))
    (F : EuclideanSpace ℝ (State A n) →L[ℝ] EuclideanSpace ℝ (State A n))
    (l : ℕ) (hl : l ≤ n) :
    ‖W.orthogonalProjection ∘L F ∘L
      ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2 ≤
      (∑ j : {j : ℕ // j ∈ Finset.Icc 1 l},
        ‖W.orthogonalProjection ∘L F ∘L
          (spectralWeightHilbertSubspace (A := A) (n := n) j.1).subtypeL‖ ^ 2) +
      ‖W.orthogonalProjection ∘L F ∘L
        (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
          (Finset.Icc (l + 1) n)).subtypeL‖ ^ 2 := by
  let Q := (activityHilbertSubspace (A := A) (n := n))ᗮ
  let G : W →L[ℝ] EuclideanSpace ℝ (State A n) :=
    (ContinuousLinearMap.adjoint F) ∘L W.subtypeL
  have h := activityOrthogonalOperator_norm_sq_le_low_add_tail
    (A := A) (n := n) W G l hl
  have hrow : ContinuousLinearMap.adjoint
      (W.orthogonalProjection ∘L F ∘L Q.subtypeL) =
        Q.orthogonalProjection ∘L G := by
    simpa only [G] using spectralProjectedBlock_adjoint Q W F
  have hblock (j : ℕ) :
      ‖(spectralWeightHilbertSubspace (A := A) (n := n) j).orthogonalProjection ∘L G‖ =
        ‖W.orthogonalProjection ∘L F ∘L
          (spectralWeightHilbertSubspace (A := A) (n := n) j).subtypeL‖ := by
    have hj := spectralProjectedBlock_adjoint
      (spectralWeightHilbertSubspace (A := A) (n := n) j) W F
    calc
      _ = ‖ContinuousLinearMap.adjoint
          (W.orthogonalProjection ∘L F ∘L
            (spectralWeightHilbertSubspace (A := A) (n := n) j).subtypeL)‖ := by
            rw [hj]
      _ = _ := ContinuousLinearMap.adjoint.norm_map _
  have htail :
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n)).orthogonalProjection ∘L G‖ =
        ‖W.orthogonalProjection ∘L F ∘L
          (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
            (Finset.Icc (l + 1) n)).subtypeL‖ := by
    have hj := spectralProjectedBlock_adjoint
      (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l + 1) n)) W F
    calc
      _ = ‖ContinuousLinearMap.adjoint
          (W.orthogonalProjection ∘L F ∘L
            (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
              (Finset.Icc (l + 1) n)).subtypeL)‖ := by
            rw [hj]
      _ = _ := ContinuousLinearMap.adjoint.norm_map _
  rw [← hrow, ContinuousLinearMap.adjoint.norm_map] at h
  simpa only [G, hblock, htail] using h

/-- The exact two-stage `V⊥ → V⊥` decomposition in Theorem 3's proof. -/
theorem activityComplementOperator_norm_sq_le_paperInteriorAndTails
    (M : Matrix (State A n) (State A n) ℝ)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n) :
    ‖activityComplementOperator M‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ((∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 M‖ ^ 2) +
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
          (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
            (Finset.Icc (l - i.1 + 1) n)).subtypeL‖ ^ 2)) +
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc l n)).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
          ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2 := by
  have houter := activityComplementOperator_norm_sq_le_outputLowTail
    (A := A) (n := n) M (l - 1) (by omega)
  rw [Nat.sub_add_cancel hlo] at houter
  have hinner (i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)}) :
      ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
        ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2 ≤
      (∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
        ‖spectralWeightBlockOperator (n := n) i.1 j.1 M‖ ^ 2) +
      ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
        (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
          (Finset.Icc (l - i.1 + 1) n)).subtypeL‖ ^ 2 := by
    have h := spectralRow_norm_sq_le_inputLowTail
      (A := A) (n := n)
      (spectralWeightHilbertSubspace (A := A) (n := n) i.1)
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M)
      (l - i.1) (by omega)
    simpa only [spectralWeightBlockOperator] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => hinner i)
  exact houter.trans (add_le_add_right hsum _)

end PairwiseIndependence

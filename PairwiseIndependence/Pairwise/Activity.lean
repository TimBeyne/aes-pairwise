import PairwiseIndependence.Pairwise.Stochastic
import PairwiseIndependence.Pairwise.LinearAlgebra
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Activity patterns and truncated differences of SHARK

An activity pattern records which coordinate differences are zero. Parallel
bijective substitution preserves this pattern. The file proves the MDS
activity counts, the paper's activity-basis coordinates, the orthogonal
projection formula, and an explicit inverse for the activity Gram matrix.
These are linear-algebra ingredients of Theorem 3.
-/

namespace PairwiseIndependence

open scoped Matrix RealInnerProductSpace

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}

/-- A bit pattern specifies exactly the zero and nonzero word differences. -/
def MatchesActivityPattern (z : Fin n → Bool) (a : State A n) : Prop :=
  ∀ i : Fin n, (a i = 0) ↔ (z i = false)

/-- The paper's set `[z]`: a coordinate is forced to zero when its bit is
zero, and unrestricted when its bit is one. -/
def InActivityBox (z : Fin n → Bool) (a : State A n) : Prop :=
  ∀ i : Fin n, z i = false → a i = 0

instance (z : Fin n → Bool) : DecidablePred (InActivityBox z : State A n → Prop) := by
  intro a
  unfold InActivityBox
  infer_instance

/-- Indicator vector `δ_[z]` of the paper's activity box. -/
noncomputable def activityBoxIndicator (z : Fin n → Bool) (a : State A n) : ℝ := by
  classical
  exact if InActivityBox z a then 1 else 0

/-- Hamming weight of an activity pattern. -/
def activityWeight (z : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => z i = true)).card

/-- Coordinatewise intersection of two activity patterns. -/
def activityMeet (x y : Fin n → Bool) (i : Fin n) : Bool :=
  x i && y i

/-- Coordinatewise symmetric difference of activity patterns. -/
def activityXor (x y : Fin n → Bool) (i : Fin n) : Bool :=
  Bool.xor (x i) (y i)

/-- The Boolean-cube weight identity used to simplify the Gram matrix. -/
theorem activityWeight_add_eq_two_meet_add_xor
    (x y : Fin n → Bool) :
    activityWeight x + activityWeight y =
      2 * activityWeight (activityMeet x y) + activityWeight (activityXor x y) := by
  have hcount (z : Fin n → Bool) :
      activityWeight z = ∑ i : Fin n, if z i = true then 1 else 0 := by
    change (Finset.univ.filter (fun i : Fin n => z i = true)).card = _
    rw [Finset.card_filter]
  calc
    activityWeight x + activityWeight y =
        ∑ i : Fin n,
          ((if x i = true then 1 else 0) + (if y i = true then 1 else 0)) := by
      rw [hcount x, hcount y, Finset.sum_add_distrib]
    _ = ∑ i : Fin n,
          (2 * (if activityMeet x y i = true then 1 else 0) +
            (if activityXor x y i = true then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hx : x i <;> cases hy : y i <;>
        simp [activityMeet, activityXor, hx, hy]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hcount, ← hcount]

omit [Fintype A] [DecidableEq A] in
/-- The intersection of two activity boxes is their coordinatewise meet. -/
theorem inActivityBox_meet_iff
    (x y : Fin n → Bool) (a : State A n) :
    InActivityBox (activityMeet x y) a ↔
      InActivityBox x a ∧ InActivityBox y a := by
  have hfalse (u v : Bool) : (u && v) = false ↔ u = false ∨ v = false := by
    cases u <;> cases v <;> decide
  constructor
  · intro h
    constructor
    · intro i hx
      exact h i ((hfalse (x i) (y i)).mpr (Or.inl hx))
    · intro i hy
      exact h i ((hfalse (x i) (y i)).mpr (Or.inr hy))
  · rintro ⟨hx, hy⟩ i hxy
    rcases (hfalse (x i) (y i)).mp hxy with hi | hi
    · exact hx i hi
    · exact hy i hi

omit [Fintype A] in
/-- Pointwise multiplication of activity-box indicators corresponds to
intersection of their activity boxes. -/
theorem activityBoxIndicator_mul
    (x y : Fin n → Bool) :
    activityBoxIndicator (A := A) x * activityBoxIndicator y =
      activityBoxIndicator (activityMeet x y) := by
  funext a
  have h := inActivityBox_meet_iff x y (a := a)
  by_cases hx : InActivityBox x a <;>
    by_cases hy : InActivityBox y a <;>
      simp [activityBoxIndicator, Pi.mul_apply, h, hx, hy]

/-- The column `δ_[z] / √(q^(weight z))` of the paper's matrix `B`, where
`q` is the alphabet size. -/
noncomputable def normalizedActivityBoxIndicator
    (z : Fin n → Bool) : State A n → ℝ :=
  (Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight z))⁻¹ •
    activityBoxIndicator z

/-- The paper's matrix `B`: each column is a normalized activity-box
indicator, indexed by an activity pattern. -/
noncomputable def activityBasisMatrix :
    Matrix (State A n) (Fin n → Bool) ℝ :=
  fun a z => normalizedActivityBoxIndicator z a

/-- Coordinates of `Bᵀ M B` are the activity-vector pairings used below. -/
theorem activityBasisMatrix_transpose_mul_mul_apply
    (M : Matrix (State A n) (State A n) ℝ) (x y : Fin n → Bool) :
    ((activityBasisMatrix (A := A) (n := n))ᵀ * M *
      activityBasisMatrix (A := A) (n := n)) y x =
      normalizedActivityBoxIndicator y ⬝ᵥ
        M *ᵥ normalizedActivityBoxIndicator x := by
  rw [Matrix.mul_assoc]
  rfl

/-- Undoing the normalization of two columns of the paper's matrix `B`. -/
theorem normalizedActivityBoxIndicator_pairing
    (M : Matrix (State A n) (State A n) ℝ) (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      (normalizedActivityBoxIndicator y ⬝ᵥ
        M *ᵥ normalizedActivityBoxIndicator x) =
      activityBoxIndicator y ⬝ᵥ M *ᵥ activityBoxIndicator x := by
  let sx := Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight x)
  let sy := Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight y)
  have hA : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩)
  have hsx : sx ≠ 0 := by
    dsimp [sx]
    positivity
  have hsy : sy ≠ 0 := by
    dsimp [sy]
    positivity
  have hroot :
      Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) =
        sy * sx := by
    rw [pow_add, mul_comm]
    exact Real.sqrt_mul (by positivity) _
  rw [hroot]
  change sy * sx * ((sy⁻¹ • activityBoxIndicator y) ⬝ᵥ
    M *ᵥ (sx⁻¹ • activityBoxIndicator x)) = _
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp [hsx, hsy]

/-- The coordinates permitted to be nonzero by an activity pattern. -/
def activitySupport (z : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z i = true)

/-- The activity pattern associated with a set of coordinates. -/
def activityPatternOfSupport (s : Finset (Fin n)) (i : Fin n) : Bool :=
  decide (i ∈ s)

theorem activityWeight_patternOfSupport (s : Finset (Fin n)) :
    activityWeight (activityPatternOfSupport s) = s.card := by
  simp [activityWeight, activityPatternOfSupport]

/-- A difference in `[z]` is freely determined by its active coordinates. -/
noncomputable def activityBoxEquiv (z : Fin n → Bool) :
    {a : State A n // InActivityBox z a} ≃ ({i : Fin n // z i = true} → A) := by
  classical
  refine {
    toFun := fun a i => a.1 i.1
    invFun := fun f => ⟨fun i => if h : z i = true then f ⟨i, h⟩ else 0, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i hz
    simp [hz]
  · intro a
    apply Subtype.ext
    funext i
    by_cases h : z i = true
    · simp [h]
    · have hz : z i = false := by cases hzi : z i <;> simp_all
      simp [h, a.2 i hz]
  · intro f
    funext i
    simp [i.2]

/-- The paper's activity box `[z]` has `q^(weight z)` differences, where
`q` is the alphabet size. -/
theorem activityBox_card (z : Fin n → Bool) :
    Fintype.card {a : State A n // InActivityBox z a} =
      Fintype.card A ^ activityWeight z := by
  classical
  calc
    Fintype.card {a : State A n // InActivityBox z a} =
        Fintype.card ({i : Fin n // z i = true} → A) :=
      Fintype.card_congr (activityBoxEquiv z)
    _ = _ := by simp [activityWeight, Fintype.card_subtype]

/-- Summing an activity-box indicator gives the cardinality of `[z]`. -/
theorem sum_activityBoxIndicator (z : Fin n → Bool) :
    (∑ a : State A n, activityBoxIndicator z a) =
      (Fintype.card A : ℝ) ^ activityWeight z := by
  classical
  calc
    (∑ a : State A n, activityBoxIndicator z a) =
        ((Finset.univ.filter (InActivityBox (A := A) z : State A n → Prop)).card : ℝ) := by
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro a _
      simp [activityBoxIndicator]
    _ = _ := by
      rw [← Fintype.card_subtype]
      exact_mod_cast activityBox_card (A := A) z

/-- The uniform-permutation difference-distribution matrix sends an
activity-box indicator to `1` at zero and to a constant elsewhere. -/
theorem uniformDifferenceDistributionMatrix_mulVec_activityBox
    (z : Fin n → Bool) (b : State A n) :
    (uniformDifferenceDistributionMatrix (State A n) *ᵥ
      activityBoxIndicator z) b =
    if b = 0 then 1 else
      ((Fintype.card A : ℝ) ^ activityWeight z - 1) /
        ((Fintype.card (State A n) - 1 : ℕ) : ℝ) := by
  classical
  change (∑ a : State A n,
    uniformDifferenceDistributionMatrix (State A n) b a *
      activityBoxIndicator z a) = _
  by_cases hb : b = 0
  · subst b
    have hterm (a : State A n) :
        uniformDifferenceDistributionMatrix (State A n) 0 a *
          activityBoxIndicator z a = if a = 0 then 1 else 0 := by
      by_cases ha : a = 0 <;> simp [uniformDifferenceDistributionMatrix_apply,
        activityBoxIndicator, InActivityBox, ha]
    simp_rw [hterm]
    simp
  · have hterm (a : State A n) :
        uniformDifferenceDistributionMatrix (State A n) b a *
          activityBoxIndicator z a =
            if a = 0 then 0 else
              activityBoxIndicator z a /
                ((Fintype.card (State A n) - 1 : ℕ) : ℝ) := by
      by_cases ha : a = 0 <;>
        simp [uniformDifferenceDistributionMatrix_apply, hb, ha, div_eq_mul_inv,
          mul_comm]
    simp_rw [hterm]
    rw [sum_except_zero, ← Finset.sum_div]
    simp only [if_neg hb]
    have hzero : activityBoxIndicator z (0 : State A n) = 1 := by
      simp [activityBoxIndicator, InActivityBox]
    rw [sum_activityBoxIndicator, hzero]
    ring

/-- The paper's unnormalised uniform-matrix activity coefficient. -/
theorem uniformDifferenceDistributionMatrix_activity_pairing
    (x y : Fin n → Bool) :
    activityBoxIndicator (A := A) y ⬝ᵥ
      uniformDifferenceDistributionMatrix (State A n) *ᵥ activityBoxIndicator x =
      1 +
        (((Fintype.card A : ℝ) ^ activityWeight x - 1) *
          ((Fintype.card A : ℝ) ^ activityWeight y - 1)) /
            ((Fintype.card (State A n) - 1 : ℕ) : ℝ) := by
  classical
  let c : ℝ :=
    ((Fintype.card A : ℝ) ^ activityWeight x - 1) /
      ((Fintype.card (State A n) - 1 : ℕ) : ℝ)
  change (∑ b : State A n, activityBoxIndicator y b *
    (uniformDifferenceDistributionMatrix (State A n) *ᵥ
      activityBoxIndicator x) b) = _
  simp_rw [uniformDifferenceDistributionMatrix_mulVec_activityBox x]
  change (∑ b : State A n,
    activityBoxIndicator y b * (if b = 0 then 1 else c)) = _
  have hterm (b : State A n) :
      activityBoxIndicator y b * (if b = 0 then 1 else c) =
        (if b = 0 then 1 else 0) +
          (if b = 0 then 0 else activityBoxIndicator y b * c) := by
    by_cases hb : b = 0 <;> simp [hb, activityBoxIndicator, InActivityBox]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ b : State A n, if b = 0 then (1 : ℝ) else 0) = 1 := by simp
  rw [hfirst, sum_except_zero, ← Finset.sum_mul]
  have hzero : activityBoxIndicator y (0 : State A n) = 1 := by
    simp [activityBoxIndicator, InActivityBox]
  rw [sum_activityBoxIndicator, hzero]
  dsimp [c]
  ring

/-- The paper's uniform-matrix coordinate formula (`unilin`), in the same
normalized activity basis `B` as the MDS coordinate formula. -/
theorem uniform_normalizedActivityBox_pairing_formula
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      (normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
        uniformDifferenceDistributionMatrix (State A n) *ᵥ
          normalizedActivityBoxIndicator x) =
      1 +
        (((Fintype.card A : ℝ) ^ activityWeight x - 1) *
          ((Fintype.card A : ℝ) ^ activityWeight y - 1)) /
            ((Fintype.card A : ℝ) ^ n - 1) := by
  rw [normalizedActivityBoxIndicator_pairing,
    uniformDifferenceDistributionMatrix_activity_pairing]
  have hcard : Fintype.card (State A n) = Fintype.card A ^ n := by
    simp [State]
  have hpos : 1 ≤ Fintype.card (State A n) :=
    Fintype.card_pos_iff.mpr ⟨(0 : State A n)⟩
  have hden : ((Fintype.card (State A n) - 1 : ℕ) : ℝ) =
      (Fintype.card A : ℝ) ^ n - 1 := by
    rw [Nat.cast_sub hpos, hcard]
    push_cast
    ring
  rw [hden]

/-- The paper's `unilin` formula stated directly as a coordinate of
`Bᵀ U B`. -/
theorem uniform_activityBasisMatrix_coordinate
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      ((activityBasisMatrix (A := A) (n := n))ᵀ *
        uniformDifferenceDistributionMatrix (State A n) *
          activityBasisMatrix (A := A) (n := n)) y x =
      1 +
        (((Fintype.card A : ℝ) ^ activityWeight x - 1) *
          ((Fintype.card A : ℝ) ^ activityWeight y - 1)) /
            ((Fintype.card A : ℝ) ^ n - 1) := by
  rw [activityBasisMatrix_transpose_mul_mul_apply]
  exact uniform_normalizedActivityBox_pairing_formula (A := A) x y

/-- Unnormalised Gram coordinates of the paper's activity-box columns. -/
theorem activityBoxIndicator_dotProduct
    (x y : Fin n → Bool) :
    activityBoxIndicator (A := A) y ⬝ᵥ activityBoxIndicator x =
      (Fintype.card A : ℝ) ^ activityWeight (activityMeet x y) := by
  classical
  have hcount : activityBoxIndicator (A := A) y ⬝ᵥ activityBoxIndicator x =
      ((Finset.univ.filter (fun a : State A n =>
        InActivityBox x a ∧ InActivityBox y a)).card : ℝ) := by
    rw [Finset.natCast_card_filter]
    change (∑ a : State A n, activityBoxIndicator y a * activityBoxIndicator x a) =
      ∑ a : State A n,
        if InActivityBox x a ∧ InActivityBox y a then (1 : ℝ) else 0
    apply Finset.sum_congr rfl
    intro a _
    by_cases hx : InActivityBox x a <;>
      by_cases hy : InActivityBox y a <;>
        simp [activityBoxIndicator, hx, hy]
  rw [hcount]
  have hset :
      (Finset.univ.filter (fun a : State A n =>
        InActivityBox x a ∧ InActivityBox y a)) =
      Finset.univ.filter (InActivityBox (activityMeet x y)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (inActivityBox_meet_iff x y a).symm
  rw [hset]
  rw [← Fintype.card_subtype]
  exact_mod_cast activityBox_card (A := A) (activityMeet x y)

/-- Normalised Gram coordinates of the paper's matrix `B`. -/
theorem normalizedActivityBoxIndicator_dotProduct
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      (normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
        normalizedActivityBoxIndicator x) =
      (Fintype.card A : ℝ) ^ activityWeight (activityMeet x y) := by
  calc
    _ = Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
        (normalizedActivityBoxIndicator y ⬝ᵥ
          (1 : Matrix (State A n) (State A n) ℝ) *ᵥ
            normalizedActivityBoxIndicator x) := by simp
    _ = activityBoxIndicator y ⬝ᵥ
        (1 : Matrix (State A n) (State A n) ℝ) *ᵥ activityBoxIndicator x :=
      normalizedActivityBoxIndicator_pairing 1 x y
    _ = _ := by simpa using activityBoxIndicator_dotProduct (A := A) x y

/-- The Gram-matrix coordinate stated in the paper: two normalized activity
columns have inner product `1 / √(q^(weight (x XOR y)))`. -/
theorem normalizedActivityBoxIndicator_dotProduct_xor
    (x y : Fin n → Bool) :
    normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
      normalizedActivityBoxIndicator x =
      1 / Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight (activityXor x y)) := by
  let q : ℝ := Fintype.card A
  let a : ℝ := q ^ activityWeight (activityMeet x y)
  let b : ℝ := Real.sqrt (q ^ activityWeight (activityXor x y))
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have hroot :
      Real.sqrt (q ^ (activityWeight x + activityWeight y)) = a * b := by
    rw [activityWeight_add_eq_two_meet_add_xor, pow_add]
    have hpow : q ^ (2 * activityWeight (activityMeet x y)) = a ^ 2 := by
      dsimp [a]
      rw [mul_comm 2, pow_mul]
    rw [hpow, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]
  have hgram := normalizedActivityBoxIndicator_dotProduct (A := A) x y
  change Real.sqrt (q ^ (activityWeight x + activityWeight y)) *
    (normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
      normalizedActivityBoxIndicator x) = a
      at hgram
  rw [hroot] at hgram
  have hcancel : b *
      (normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
        normalizedActivityBoxIndicator x) = 1 := by
    have hmul : a *
        (b * (normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
          normalizedActivityBoxIndicator x)) = a * 1 := by
      nlinarith [hgram]
    exact mul_left_cancel₀ (ne_of_gt ha) hmul
  apply (eq_div_iff hb).2
  simpa [b, mul_comm] using hcancel

/-- The Gram-matrix identity `Bᵀ B` from the paper, stated directly in
matrix coordinates. -/
theorem activityBasisMatrix_gram_coordinate
    (x y : Fin n → Bool) :
    ((activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n)) y x =
      1 / Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight (activityXor x y)) := by
  change normalizedActivityBoxIndicator (A := A) y ⬝ᵥ
    normalizedActivityBoxIndicator x = _
  exact normalizedActivityBoxIndicator_dotProduct_xor (A := A) x y

/-- An activity box is an additive subgroup of the state space. -/
def activityBoxAddSubgroup (z : Fin n → Bool) : AddSubgroup (State A n) where
  carrier := {a | InActivityBox z a}
  zero_mem' := by
    intro i _
    rfl
  add_mem' := by
    intro a b ha hb i hz
    simp [ha i hz, hb i hz]
  neg_mem' := by
    intro a ha i hz
    simp [ha i hz]

omit [Fintype A] [DecidableEq A] in
/-- Restricting the permitted support shrinks an activity box. -/
theorem activityBoxAddSubgroup_mono_support
    (x : Fin n → Bool) (s : Finset (Fin n))
    (hs : s ⊆ activitySupport x) :
    activityBoxAddSubgroup (A := A) (activityPatternOfSupport s) ≤
      activityBoxAddSubgroup (A := A) x := by
  intro a ha
  intro i hxi
  have his : i ∉ s := by
    intro hi
    have hix := hs hi
    simp [activitySupport, hxi] at hix
  exact ha i (by simp [activityPatternOfSupport, his])

/-- Restrict the output of a linear layer to positions that `[y]` forces to
zero, with input differences drawn from `[x]`. -/
def activityOutputRestriction
    (L : State A n ≃+ State A n) (x y : Fin n → Bool) :
    activityBoxAddSubgroup (A := A) x →+ ({i : Fin n // y i = false} → A) where
  toFun a i := (L a.1) i.1
  map_zero' := by
    funext i
    simp
  map_add' := by
    intro a b
    funext i
    simp

omit [Fintype A] in
/-- The support of a difference in `[z]` has at most the weight of `z`. -/
theorem activeCoordinates_le_activityWeight_of_inActivityBox
    (z : Fin n → Bool) (a : State A n) (ha : InActivityBox z a) :
    activeCoordinates a ≤ activityWeight z := by
  unfold activeCoordinates activityWeight
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  cases hz : z i with
  | false => exact (hi (ha i hz)).elim
  | true => rfl

omit [Fintype A] in
/-- The paper's low-weight MDS intersection statement: if the two activity
weights sum to at most `n`, the only difference in `[x]` mapped into `[y]`
by an MDS layer is zero. -/
theorem IsMDS.eq_zero_of_activityBoxes
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) (a : State A n)
    (ha : InActivityBox x a) (hb : InActivityBox y (L a))
    (hweight : activityWeight x + activityWeight y ≤ n) : a = 0 := by
  by_contra hne
  have hbranch := hMDS a hne
  have hx := activeCoordinates_le_activityWeight_of_inActivityBox x a ha
  have hy := activeCoordinates_le_activityWeight_of_inActivityBox y (L a) hb
  omega

omit [Fintype A] in
/-- The MDS branch-number condition gives full column rank for a restricted
linear layer whenever the input and output activity weights sum to at most
`n`. This is the injective half of the paper's full-rank lemma. -/
theorem activityOutputRestriction_injective_of_low_weight
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool)
    (hweight : activityWeight x + activityWeight y ≤ n) :
    Function.Injective (activityOutputRestriction L x y) := by
  intro a b hab
  have hinput : InActivityBox x (a.1 - b.1) := by
    intro i hz
    simp [a.2 i hz, b.2 i hz]
  have houtput : InActivityBox y (L (a.1 - b.1)) := by
    intro i hz
    have hi := congrFun hab ⟨i, hz⟩
    change (L a.1) i = (L b.1) i at hi
    simp [map_sub, hi]
  have hzero := hMDS.eq_zero_of_activityBoxes L x y (a.1 - b.1)
    hinput houtput hweight
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

/-- The number of output coordinates forced to zero by `[y]`, plus the number
of active coordinates of `[y]`, is `n`. -/
theorem activityWeight_add_forcedZero_count (y : Fin n → Bool) :
    activityWeight y + Fintype.card {i : Fin n // y i = false} = n := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun i : Fin n => y i = true)
  have hfilter :
      (Finset.univ.filter (fun i : Fin n => ¬ y i = true)) =
      Finset.univ.filter (fun i : Fin n => y i = false) := by
    ext i
    cases hy : y i <;> simp [hy]
  rw [hfilter] at h
  simpa [activityWeight] using h

/-- A square restricted MDS block is bijective. This follows from the branch
number and the equal cardinalities of its input and output activity spaces. -/
theorem activityOutputRestriction_bijective_of_equal_weight
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool)
    (hweight : activityWeight x + activityWeight y = n) :
    Function.Bijective (activityOutputRestriction L x y) := by
  classical
  letI : Fintype (activityBoxAddSubgroup (A := A) x) := Fintype.ofFinite _
  have hinj := activityOutputRestriction_injective_of_low_weight
    L hMDS x y (Nat.le_of_eq hweight)
  apply (Fintype.bijective_iff_injective_and_card
    (activityOutputRestriction L x y)).2
  refine ⟨hinj, ?_⟩
  have hinput :
      Fintype.card (activityBoxAddSubgroup (A := A) x) =
        Fintype.card A ^ activityWeight x := by
    calc
      Fintype.card (activityBoxAddSubgroup (A := A) x) =
          Fintype.card {a : State A n // InActivityBox x a} :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := activityBox_card x
  have houtput :
      Fintype.card ({i : Fin n // y i = false} → A) =
        Fintype.card A ^ Fintype.card {i : Fin n // y i = false} := by
    simp
  rw [hinput, houtput]
  congr 1
  have hy := activityWeight_add_forcedZero_count y
  omega

/-- The full-row-rank half of the paper's MDS lemma: if the activity weights
sum to at least `n`, every assignment to the forced-zero output coordinates
is attained by an input in `[x]`. -/
theorem activityOutputRestriction_surjective_of_high_weight
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool)
    (hweight : n ≤ activityWeight x + activityWeight y) :
    Function.Surjective (activityOutputRestriction L x y) := by
  let m := Fintype.card {i : Fin n // y i = false}
  have hy : activityWeight y + m = n := activityWeight_add_forcedZero_count y
  have hm : m ≤ (activitySupport x).card := by
    change m ≤ activityWeight x
    omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hm
  have hsum : activityWeight (activityPatternOfSupport s) + activityWeight y = n := by
    rw [activityWeight_patternOfSupport, hcard]
    omega
  have hbij := activityOutputRestriction_bijective_of_equal_weight
    L hMDS (activityPatternOfSupport s) y hsum
  intro out
  obtain ⟨a, ha⟩ := hbij.2 out
  have hsub := activityBoxAddSubgroup_mono_support (A := A) x s hs
  exact ⟨⟨a.1, hsub a.2⟩, ha⟩

/-- The number of linear-layer transitions from activity box `[x]` to `[y]`. -/
noncomputable def linearActivityIntersectionCount
    (L : State A n ≃+ State A n) (x y : Fin n → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun a : State A n => InActivityBox x a ∧ InActivityBox y (L a))).card

/-- The compatible differences are the kernel of the restricted output map. -/
noncomputable def linearActivityIntersectionEquivKer
    (L : State A n ≃+ State A n) (x y : Fin n → Bool) :
    {a : State A n // InActivityBox x a ∧ InActivityBox y (L a)} ≃
      (activityOutputRestriction L x y).ker := by
  classical
  refine {
    toFun := fun a => ⟨⟨a.1, a.2.1⟩, ?_⟩
    invFun := fun a => ⟨a.1.1, ⟨a.1.2, ?_⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · change (activityOutputRestriction L x y) ⟨a.1, a.2.1⟩ = 0
    funext i
    exact a.2.2 i.1 i.2
  · intro i hy
    have hker := a.2
    change (activityOutputRestriction L x y) a.1 = 0 at hker
    exact congrFun hker ⟨i, hy⟩
  · intro a
    apply Subtype.ext
    rfl
  · intro a
    apply Subtype.ext
    rfl

/-- The activity intersection count equals the kernel cardinality of the
restricted linear map. -/
theorem linearActivityIntersectionCount_eq_card_ker
    (L : State A n ≃+ State A n) (x y : Fin n → Bool) :
    linearActivityIntersectionCount L x y =
      Nat.card (activityOutputRestriction L x y).ker := by
  classical
  calc
    linearActivityIntersectionCount L x y =
        Fintype.card {a : State A n //
          InActivityBox x a ∧ InActivityBox y (L a)} := by
      simp [linearActivityIntersectionCount, Fintype.card_subtype]
    _ = Nat.card (activityOutputRestriction L x y).ker := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (linearActivityIntersectionEquivKer L x y)

/-- The high-weight case of the paper's MDS activity counting formula. -/
theorem linearActivityIntersectionCount_eq_pow_of_high_weight
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool)
    (hweight : n ≤ activityWeight x + activityWeight y) :
    linearActivityIntersectionCount L x y =
      Fintype.card A ^ (activityWeight x + activityWeight y - n) := by
  classical
  let f := activityOutputRestriction L x y
  have hsurj : Function.Surjective f :=
    activityOutputRestriction_surjective_of_high_weight L hMDS x y hweight
  have hsource : Nat.card (activityBoxAddSubgroup (A := A) x) =
      Fintype.card A ^ activityWeight x := by
    calc
      _ = Nat.card {a : State A n // InActivityBox x a} :=
        Nat.card_congr (Equiv.refl _)
      _ = Fintype.card {a : State A n // InActivityBox x a} :=
        Nat.card_eq_fintype_card
      _ = _ := activityBox_card x
  have htarget : Nat.card ({i : Fin n // y i = false} → A) =
      Fintype.card A ^ Fintype.card {i : Fin n // y i = false} := by
    rw [Nat.card_eq_fintype_card]
    simp
  have hcard := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, f.range_eq_top_of_surjective hsurj] at hcard
  rw [AddSubgroup.card_top] at hcard
  rw [hsource, htarget] at hcard
  rw [linearActivityIntersectionCount_eq_card_ker]
  have hy := activityWeight_add_forcedZero_count y
  have hm : Fintype.card {i : Fin n // y i = false} ≤ activityWeight x := by omega
  have hexp : activityWeight x =
      Fintype.card {i : Fin n // y i = false} +
        (activityWeight x + activityWeight y - n) := by omega
  rw [hexp, pow_add] at hcard
  have hpositive : 0 < Fintype.card A ^ Fintype.card {i : Fin n // y i = false} := by
    have hA : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
    positivity
  nlinarith

/-- The first case of the paper's MDS counting formula. -/
theorem linearActivityIntersectionCount_eq_one_of_low_weight
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool)
    (hweight : activityWeight x + activityWeight y ≤ n) :
    linearActivityIntersectionCount L x y = 1 := by
  classical
  have hset :
      (Finset.univ.filter
        (fun a : State A n => InActivityBox x a ∧ InActivityBox y (L a))) =
          {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hb⟩
      exact hMDS.eq_zero_of_activityBoxes L x y a ha hb hweight
    · rintro rfl
      simp [InActivityBox]
  simp [linearActivityIntersectionCount, hset]

/-- The complete MDS counting formula behind the paper's `Bᵀ D^L B`
coordinates, before normalization by square roots of activity-box sizes. -/
theorem linearActivityIntersectionCount_formula
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    linearActivityIntersectionCount L x y =
      if n + 1 ≤ activityWeight x + activityWeight y then
        Fintype.card A ^ (activityWeight x + activityWeight y - n)
      else 1 := by
  by_cases h : n + 1 ≤ activityWeight x + activityWeight y
  · simp only [if_pos h]
    exact linearActivityIntersectionCount_eq_pow_of_high_weight
      L hMDS x y (by omega)
  · simp only [if_neg h]
    exact linearActivityIntersectionCount_eq_one_of_low_weight
      L hMDS x y (by omega)

/-- The activity-box matrix coefficient of a linear layer is exactly the
number of compatible differences. This is the unnormalised coordinate used
in the paper's truncated-differential analysis. -/
theorem linearActivityIntersectionCount_eq_differenceDistributionMatrix_pairing
    (L : State A n ≃+ State A n) (x y : Fin n → Bool) :
    (linearActivityIntersectionCount L x y : ℝ) =
      activityBoxIndicator y ⬝ᵥ
        deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *ᵥ activityBoxIndicator x := by
  classical
  rw [linearActivityIntersectionCount, Finset.natCast_card_filter]
  change (∑ a : State A n,
    if InActivityBox x a ∧ InActivityBox y (L a) then (1 : ℝ) else 0) =
      ∑ b : State A n, activityBoxIndicator y b *
        ∑ a : State A n,
          deterministicDifferenceDistributionMatrix
            (fun c : State A n => L c) b a * activityBoxIndicator x a
  have hL (b a : State A n) :
      deterministicDifferenceDistributionMatrix
        (fun c : State A n => L c) b a =
          if L a = b then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom b a
  simp_rw [hL]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : InActivityBox x a <;>
    by_cases hy : InActivityBox y (L a) <;>
      simp [activityBoxIndicator, hx, hy]

/-- The paper's complete unnormalised activity-coordinate formula for the
difference-distribution matrix of an MDS linear layer. -/
theorem linear_differenceDistributionMatrix_activity_pairing_formula
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    activityBoxIndicator y ⬝ᵥ
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *ᵥ activityBoxIndicator x =
      if n + 1 ≤ activityWeight x + activityWeight y then
        (Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y - n)
      else 1 := by
  rw [← linearActivityIntersectionCount_eq_differenceDistributionMatrix_pairing,
    linearActivityIntersectionCount_formula L hMDS x y]
  split_ifs <;> simp

/-- The paper's normalized `Bᵀ D^L B` coordinate formula (`mdslin`). The
factor on the left is `√(q^(weight x + weight y))`. -/
theorem linear_normalizedActivityBox_pairing_formula
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      (normalizedActivityBoxIndicator y ⬝ᵥ
        deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *ᵥ normalizedActivityBoxIndicator x) =
      if n + 1 ≤ activityWeight x + activityWeight y then
        (Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y - n)
      else 1 := by
  rw [normalizedActivityBoxIndicator_pairing]
  exact linear_differenceDistributionMatrix_activity_pairing_formula L hMDS x y

/-- The paper's `mdslin` formula stated directly as a coordinate of
`Bᵀ D^L B`. -/
theorem linear_activityBasisMatrix_coordinate
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      ((activityBasisMatrix (A := A) (n := n))ᵀ *
        deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) *
          activityBasisMatrix (A := A) (n := n)) y x =
      if n + 1 ≤ activityWeight x + activityWeight y then
        (Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y - n)
      else 1 := by
  rw [activityBasisMatrix_transpose_mul_mul_apply]
  exact linear_normalizedActivityBox_pairing_formula L hMDS x y

/-- The paper's subspace `V`, spanned by the activity-box indicators. -/
noncomputable def activitySubspace : Submodule ℝ (State A n → ℝ) :=
  Submodule.span ℝ (Set.range (activityBoxIndicator (A := A) (n := n)))

omit [Fintype A] in
/-- The paper's activity subspace is closed under pointwise multiplication.
This follows from intersection of activity boxes. -/
theorem activitySubspace_mul_mem
    (v w : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n))
    (hw : w ∈ activitySubspace (A := A) (n := n)) :
    v * w ∈ activitySubspace (A := A) (n := n) := by
  have hfixed (z : Fin n → Bool) (u : State A n → ℝ)
      (hu : u ∈ activitySubspace (A := A) (n := n)) :
      activityBoxIndicator z * u ∈ activitySubspace (A := A) (n := n) := by
    change u ∈ Submodule.span ℝ
      (Set.range (activityBoxIndicator (A := A) (n := n))) at hu
    induction hu using Submodule.span_induction with
    | mem _ h =>
        rcases h with ⟨y, rfl⟩
        rw [activityBoxIndicator_mul]
        exact Submodule.subset_span ⟨activityMeet z y, rfl⟩
    | zero => simp
    | add u₁ u₂ _ _ ih₁ ih₂ =>
        rw [mul_add]
        exact (activitySubspace (A := A) (n := n)).add_mem ih₁ ih₂
    | smul t u _ ih =>
        have hs : activityBoxIndicator z * (t • u) =
            t • (activityBoxIndicator z * u) := by
          funext a
          simp [Pi.mul_apply, Pi.smul_apply, mul_left_comm]
        rw [hs]
        exact (activitySubspace (A := A) (n := n)).smul_mem t ih
  change v ∈ Submodule.span ℝ
    (Set.range (activityBoxIndicator (A := A) (n := n))) at hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
      rcases h with ⟨z, rfl⟩
      exact hfixed z w hw
  | zero => simp
  | add v₁ v₂ _ _ ih₁ ih₂ =>
      rw [add_mul]
      exact (activitySubspace (A := A) (n := n)).add_mem ih₁ ih₂
  | smul t v _ ih =>
      have hs : (t • v) * w = t • (v * w) := by
        funext a
        simp [Pi.mul_apply, Pi.smul_apply, mul_assoc]
      rw [hs]
      exact (activitySubspace (A := A) (n := n)).smul_mem t ih

/-- The same activity subspace as a subspace of the Euclidean difference-vector
space, so the paper's orthogonal projection is available. -/
noncomputable def activityHilbertSubspace :
    Submodule ℝ (EuclideanSpace ℝ (State A n)) :=
  Submodule.span ℝ (Set.range (fun z : Fin n → Bool =>
    (WithLp.toLp 2 (activityBoxIndicator (A := A) z) :
      EuclideanSpace ℝ (State A n))))

/-- The Euclidean activity subspace is exactly the image of the algebraic
activity subspace under the canonical linear equivalence. -/
theorem activityHilbertSubspace_eq_map :
    activityHilbertSubspace (A := A) (n := n) =
      (activitySubspace (A := A) (n := n)).map
        (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).symm.toLinearMap := by
  unfold activityHilbertSubspace activitySubspace
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨activityBoxIndicator z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

/-- Membership in the Euclidean activity subspace is equivalent to membership
of the underlying function in the paper's algebraic `V`. -/
theorem mem_activityHilbertSubspace_iff
    (v : EuclideanSpace ℝ (State A n)) :
    v ∈ activityHilbertSubspace (A := A) (n := n) ↔
      (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v ∈
        activitySubspace (A := A) (n := n) := by
  rw [activityHilbertSubspace_eq_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨(WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v, hv, by simp⟩

/-- The paper's orthogonal projection `π_V`. -/
noncomputable def activityOrthogonalProjection :
    EuclideanSpace ℝ (State A n) →L[ℝ]
      activityHilbertSubspace (A := A) (n := n) :=
  (activityHilbertSubspace (A := A) (n := n)).orthogonalProjection

/-- The paper's truncated-differential operator `π_V M i_V`. -/
noncomputable def activityTruncatedOperator
    (M : Matrix (State A n) (State A n) ℝ) :
    activityHilbertSubspace (A := A) (n := n) →L[ℝ]
      activityHilbertSubspace (A := A) (n := n) :=
  activityOrthogonalProjection (A := A) (n := n) ∘L
    (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M) ∘L
      (activityHilbertSubspace (A := A) (n := n)).subtypeL

omit [AddCommGroup A] [DecidableEq A] in
/-- On real difference vectors, Euclidean inner product agrees with the
paper's dot product of coordinate functions. -/
theorem euclidean_inner_eq_dotProduct
    (u v : EuclideanSpace ℝ (State A n)) :
    ⟪u, v⟫ =
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) u) ⬝ᵥ
        ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [WithLp.linearEquiv_apply, dotProduct_comm]

/-- Matrix coefficients of the truncated operator are the paper's Euclidean
pairings of activity vectors with the original matrix. -/
theorem activityTruncatedOperator_inner
    (M : Matrix (State A n) (State A n) ℝ)
    (v w : activityHilbertSubspace (A := A) (n := n)) :
    ⟪v, activityTruncatedOperator M w⟫ =
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) (v : EuclideanSpace ℝ (State A n))) ⬝ᵥ
        M *ᵥ
          ((WithLp.linearEquiv 2 ℝ (State A n → ℝ))
            (w : EuclideanSpace ℝ (State A n))) := by
  change ⟪v,
    (activityHilbertSubspace (A := A) (n := n)).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M w)⟫ = _
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
  rw [euclidean_inner_eq_dotProduct]
  simp [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM]

/-- Equality of all activity-vector pairings implies equality of the
truncated-differential operators `π_V M i_V` and `π_V N i_V`. -/
theorem activityTruncatedOperator_eq_of_pairing_eq
    (M N : Matrix (State A n) (State A n) ℝ)
    (hpair : ∀ v w : State A n → ℝ,
      v ∈ activitySubspace (A := A) (n := n) →
      w ∈ activitySubspace (A := A) (n := n) →
        v ⬝ᵥ M *ᵥ w = v ⬝ᵥ N *ᵥ w) :
    activityTruncatedOperator M = activityTruncatedOperator N := by
  apply ContinuousLinearMap.ext
  intro w
  have hcoeff (v : activityHilbertSubspace (A := A) (n := n)) :
      ⟪v, activityTruncatedOperator M w⟫ =
        ⟪v, activityTruncatedOperator N w⟫ := by
    rw [activityTruncatedOperator_inner, activityTruncatedOperator_inner]
    exact hpair _ _
      ((mem_activityHilbertSubspace_iff (v : EuclideanSpace ℝ (State A n))).mp v.2)
      ((mem_activityHilbertSubspace_iff (w : EuclideanSpace ℝ (State A n))).mp w.2)
  let t := activityTruncatedOperator M w - activityTruncatedOperator N w
  have ht : ⟪t, t⟫ = 0 := by
    change ⟪t, activityTruncatedOperator M w - activityTruncatedOperator N w⟫ = 0
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (hcoeff t)
  have hzero := inner_self_eq_zero.mp ht
  exact sub_eq_zero.mp hzero

omit [Fintype A] in
/-- Every activity-box indicator belongs to the paper's activity subspace. -/
theorem activityBoxIndicator_mem_activitySubspace (z : Fin n → Bool) :
    activityBoxIndicator (A := A) z ∈ activitySubspace (A := A) (n := n) := by
  exact Submodule.subset_span ⟨z, rfl⟩

/-- Indicator vector of one exact activity class. These vectors span the same
activity subspace as the paper's indicators of `[z]`. -/
noncomputable def activityClassIndicator (z : Fin n → Bool) (a : State A n) : ℝ := by
  classical
  exact if MatchesActivityPattern z a then 1 else 0

/-- The exact zero/nonzero activity pattern of a difference. -/
def activityPatternOfDifference (a : State A n) (i : Fin n) : Bool :=
  decide (a i ≠ 0)

omit [Fintype A] in
/-- A difference belongs to exactly one exact activity class. -/
theorem matchesActivityPattern_iff_eq_pattern
    (z : Fin n → Bool) (a : State A n) :
    MatchesActivityPattern z a ↔ z = activityPatternOfDifference a := by
  constructor
  · intro h
    funext i
    by_cases ha : a i = 0
    · have hz := (h i).mp ha
      simp [activityPatternOfDifference, ha, hz]
    · have hz : z i = true := by
        cases hzi : z i with
        | false => exact (ha ((h i).mpr hzi)).elim
        | true => rfl
      simp [activityPatternOfDifference, ha, hz]
  · intro h
    subst z
    intro i
    by_cases ha : a i = 0 <;>
      simp [activityPatternOfDifference, ha]

omit [Fintype A] in
/-- A class indicator is a Kronecker delta at the activity pattern of its
argument. -/
theorem activityClassIndicator_eq_ite_pattern
    (z : Fin n → Bool) (a : State A n) :
    activityClassIndicator z a =
      if z = activityPatternOfDifference a then 1 else 0 := by
  simp [activityClassIndicator, matchesActivityPattern_iff_eq_pattern]

omit [Fintype A] in
/-- An activity box contains a difference exactly when that difference's
active-coordinate set is allowed by the box pattern. -/
theorem inActivityBox_iff_support_subset
    (z : Fin n → Bool) (a : State A n) :
    InActivityBox z a ↔
      activitySupport (activityPatternOfDifference a) ⊆ activitySupport z := by
  constructor
  · intro h i hi
    have hne : a i ≠ 0 := by
      simpa [activitySupport, activityPatternOfDifference] using hi
    by_cases hz : z i = true
    · simp [activitySupport, hz]
    · have hfalse : z i = false := by cases hzi : z i <;> simp_all
      exact (hne (h i hfalse)).elim
  · intro h i hz
    by_contra hne
    have hi : i ∈ activitySupport (activityPatternOfDifference a) := by
      simp [activitySupport, activityPatternOfDifference, hne]
    have hzi := h hi
    simp [activitySupport, hz] at hzi

omit [Fintype A] in
/-- Each activity-box indicator is the sum of the exact activity classes
whose active coordinates it allows. -/
theorem activityBoxIndicator_eq_sum_classes
    (z : Fin n → Bool) :
    activityBoxIndicator (A := A) z =
      ∑ w : Fin n → Bool,
        if activitySupport w ⊆ activitySupport z then
          activityClassIndicator w else 0 := by
  classical
  funext a
  simp only [Finset.sum_apply]
  change activityBoxIndicator z a =
    ∑ w : Fin n → Bool,
      (if activitySupport w ⊆ activitySupport z then
        activityClassIndicator w else 0) a
  simp_rw [ite_apply, activityClassIndicator_eq_ite_pattern]
  simp only [Pi.zero_apply]
  have hterm (w : Fin n → Bool) :
      (if activitySupport w ⊆ activitySupport z then
          (if w = activityPatternOfDifference a then (1 : ℝ) else 0)
        else 0) =
        if w = activityPatternOfDifference a then
          (if activitySupport (activityPatternOfDifference a) ⊆
            activitySupport z then 1 else 0)
        else 0 := by
    by_cases hw : w = activityPatternOfDifference a <;> simp [hw]
  simp_rw [hterm]
  simp [activityBoxIndicator, inActivityBox_iff_support_subset]

/-- The activity box forcing just coordinate `i` to zero. -/
def singleZeroActivityPattern (i j : Fin n) : Bool :=
  if j = i then false else true

omit [Fintype A] in
/-- The indicator of a single zero coordinate is one of the paper's
activity-box indicators. -/
theorem activityBoxIndicator_singleZero
    (i : Fin n) (a : State A n) :
    activityBoxIndicator (singleZeroActivityPattern i) a =
      if a i = 0 then 1 else 0 := by
  have hiff : InActivityBox (singleZeroActivityPattern i) a ↔ a i = 0 := by
    constructor
    · intro h
      exact h i (by simp [singleZeroActivityPattern])
    · intro h j hj
      by_cases hji : j = i
      · simpa [hji] using h
      · simp [singleZeroActivityPattern, hji] at hj
  simp [activityBoxIndicator, hiff]

/-- A factor selecting either the zero or nonzero class at coordinate `i`. -/
noncomputable def activityCoordinateSelector
    (z : Fin n → Bool) (i : Fin n) : State A n → ℝ :=
  if z i = false then activityBoxIndicator (singleZeroActivityPattern i)
  else 1 - activityBoxIndicator (singleZeroActivityPattern i)

omit [Fintype A] in
theorem activityCoordinateSelector_apply
    (z : Fin n → Bool) (i : Fin n) (a : State A n) :
    activityCoordinateSelector z i a =
      if (a i = 0 ↔ z i = false) then 1 else 0 := by
  by_cases hz : z i = false <;>
    by_cases ha : a i = 0 <;>
      simp [activityCoordinateSelector, hz,
        activityBoxIndicator_singleZero, ha]

omit [Fintype A] in
/-- An exact activity-class indicator is the product of the corresponding
coordinate selectors. -/
theorem activityClassIndicator_eq_prod
    (z : Fin n → Bool) :
    activityClassIndicator (A := A) z =
      ∏ i : Fin n, activityCoordinateSelector z i := by
  classical
  funext a
  change (if MatchesActivityPattern z a then (1 : ℝ) else 0) = _
  simp_rw [Finset.prod_apply, activityCoordinateSelector_apply]
  rw [Fintype.prod_boole]
  simp [MatchesActivityPattern]

omit [Fintype A] in
/-- The constant-one function is the activity-box indicator with every
coordinate unrestricted. -/
theorem one_mem_activitySubspace :
    (1 : State A n → ℝ) ∈ activitySubspace (A := A) (n := n) := by
  have h : activityBoxIndicator (A := A) (fun _ : Fin n => true) = 1 := by
    funext a
    simp [activityBoxIndicator, InActivityBox]
  rw [← h]
  exact activityBoxIndicator_mem_activitySubspace (A := A) (fun _ => true)

omit [Fintype A] in
/-- Each single-coordinate zero/nonzero selector belongs to `V`. -/
theorem activityCoordinateSelector_mem_activitySubspace
    (z : Fin n → Bool) (i : Fin n) :
    activityCoordinateSelector (A := A) z i ∈
      activitySubspace (A := A) (n := n) := by
  by_cases hz : z i = false
  · simp only [activityCoordinateSelector, if_pos hz]
    exact activityBoxIndicator_mem_activitySubspace (A := A)
      (singleZeroActivityPattern i)
  · simp only [activityCoordinateSelector, if_neg hz]
    exact (activitySubspace (A := A) (n := n)).sub_mem
      one_mem_activitySubspace
      (activityBoxIndicator_mem_activitySubspace (A := A)
        (singleZeroActivityPattern i))

omit [Fintype A] in
/-- Every exact activity-class indicator belongs to the paper's subspace
`V`, as a product of its coordinate selectors. -/
theorem activityClassIndicator_mem_activitySubspace
    (z : Fin n → Bool) :
    activityClassIndicator (A := A) z ∈
      activitySubspace (A := A) (n := n) := by
  rw [activityClassIndicator_eq_prod]
  have hprod (s : Finset (Fin n)) :
      (∏ i ∈ s, activityCoordinateSelector (A := A) z i) ∈
        activitySubspace (A := A) (n := n) := by
    induction s using Finset.induction_on with
    | empty => simpa using one_mem_activitySubspace (A := A) (n := n)
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi]
        exact activitySubspace_mul_mem _ _
          (activityCoordinateSelector_mem_activitySubspace z i) ih
  exact hprod Finset.univ

omit [Fintype A] in
/-- The activity-box indicators and the disjoint exact activity-class
indicators span the same subspace `V`. -/
theorem activitySubspace_eq_span_classes :
    activitySubspace (A := A) (n := n) =
      Submodule.span ℝ
        (Set.range (activityClassIndicator (A := A) (n := n))) := by
  apply le_antisymm
  · rw [activitySubspace]
    apply Submodule.span_le.mpr
    rintro v ⟨z, rfl⟩
    rw [activityBoxIndicator_eq_sum_classes]
    apply Submodule.sum_mem
    intro w _
    by_cases hw : activitySupport w ⊆ activitySupport z
    · simp only [if_pos hw]
      exact Submodule.subset_span ⟨w, rfl⟩
    · simp [hw]
  · apply Submodule.span_le.mpr
    rintro v ⟨z, rfl⟩
    exact activityClassIndicator_mem_activitySubspace z

/-- A concrete representative of an exact activity class, using any chosen
nonzero word difference `u`. -/
def activityRepresentative (u : A) (z : Fin n → Bool) : State A n :=
  fun i => if z i = true then u else 0

omit [Fintype A] in
/-- The representative has exactly its designated activity pattern. -/
theorem activityPatternOfDifference_representative
    (u : A) (hu : u ≠ 0) (z : Fin n → Bool) :
    activityPatternOfDifference (activityRepresentative u z) = z := by
  funext i
  cases hz : z i <;>
    simp [activityPatternOfDifference, activityRepresentative, hz, hu]

omit [Fintype A] in
/-- The exact activity-class indicators are linearly independent whenever
the alphabet has a nonzero element. -/
theorem activityClassIndicator_linearIndependent
    (u : A) (hu : u ≠ 0) :
    LinearIndependent ℝ
      (activityClassIndicator (A := A) (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g h z
  have hz := congrFun h (activityRepresentative u z)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hz
  have hrep (w : Fin n → Bool) :
      activityClassIndicator w (activityRepresentative u z) =
        if w = z then 1 else 0 := by
    rw [activityClassIndicator_eq_ite_pattern,
      activityPatternOfDifference_representative u hu z]
  simp_rw [hrep] at hz
  simpa using hz

omit [Fintype A] in
/-- The paper's activity-box indicators are linearly independent when the
alphabet contains a nonzero element. -/
theorem activityBoxIndicator_linearIndependent
    (u : A) (hu : u ≠ 0) :
    LinearIndependent ℝ
      (activityBoxIndicator (A := A) (n := n)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  have hclass := activityClassIndicator_linearIndependent (n := n) u hu
  have hdim := linearIndependent_iff_card_eq_finrank_span.mp hclass
  change Fintype.card (Fin n → Bool) =
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (activityClassIndicator (A := A) (n := n)))) at hdim
  change Fintype.card (Fin n → Bool) =
    Module.finrank ℝ
      (Submodule.span ℝ
        (Set.range (activityBoxIndicator (A := A) (n := n))))
  rw [← activitySubspace_eq_span_classes (A := A) (n := n)] at hdim
  exact hdim

/-- The normalized columns of the paper's matrix `B` are linearly
independent. -/
theorem normalizedActivityBoxIndicator_linearIndependent
    (u : A) (hu : u ≠ 0) :
    LinearIndependent ℝ
      (normalizedActivityBoxIndicator (A := A) (n := n)) := by
  classical
  have hbox := activityBoxIndicator_linearIndependent (n := n) u hu
  rw [Fintype.linearIndependent_iff]
  intro g hg z
  let c (w : Fin n → Bool) : ℝ :=
    (Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight w))⁻¹
  have hraw :
      (∑ w : Fin n → Bool,
        (g w * c w) • activityBoxIndicator (A := A) w) = 0 := by
    simpa only [normalizedActivityBoxIndicator, c, smul_smul] using hg
  have hz := (Fintype.linearIndependent_iff.mp hbox) _ hraw z
  have hc : c z ≠ 0 := by
    dsimp [c]
    have hA : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩)
    positivity
  exact (mul_eq_zero.mp hz).resolve_right hc

/-- The paper's Gram matrix `Bᵀ B` is invertible when the alphabet has a
nonzero element. Thus the inverse in its projection-coordinate formula is
mathematically justified. -/
theorem activityBasisMatrix_gram_isUnit
    (u : A) (hu : u ≠ 0) :
    IsUnit ((activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n)) := by
  let B := activityBasisMatrix (A := A) (n := n)
  have hnorm := normalizedActivityBoxIndicator_linearIndependent (n := n) u hu
  change LinearIndependent ℝ B.col at hnorm
  have hB : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hnorm
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro c d hcd
  have hG : (Bᵀ * B) *ᵥ (c - d) = 0 := by
    rw [Matrix.mulVec_sub, hcd, sub_self]
  rw [← Matrix.mulVec_mulVec] at hG
  have hdot : (c - d) ⬝ᵥ Bᵀ *ᵥ (B *ᵥ (c - d)) =
      (B *ᵥ (c - d)) ⬝ᵥ (B *ᵥ (c - d)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hself : (B *ᵥ (c - d)) ⬝ᵥ (B *ᵥ (c - d)) = 0 := by
    rw [← hdot, hG]
    simp
  have hBzero := dotProduct_self_eq_zero.mp hself
  have hvzero : c - d = 0 := hB (by simpa using hBzero)
  exact sub_eq_zero.mp hvzero

/-- The normalized activity Gram matrix is positive definite, a stronger
form of its invertibility needed for orthonormalizing the activity basis. -/
theorem activityBasisMatrix_gram_posDef
    (u : A) (hu : u ≠ 0) :
    ((activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n)).PosDef := by
  let B := activityBasisMatrix (A := A) (n := n)
  have hnorm := normalizedActivityBoxIndicator_linearIndependent (n := n) u hu
  change LinearIndependent ℝ B.col at hnorm
  have hB : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hnorm
  simpa [B, Matrix.conjTranspose] using
    (Matrix.PosDef.conjTranspose_mul_self B hB)

/-- The inverse square root `R` of the positive-definite activity Gram
matrix, used to orthonormalize the paper's basis `B`. -/
noncomputable def activityGramInverseSquareRoot
    (u : A) (hu : u ≠ 0) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  (activityBasisMatrix_gram_posDef u hu).posSemidef.sqrt⁻¹

/-- The columns of `B R` are orthonormal: `Rᵀ (BᵀB) R = I`. -/
theorem activityGramInverseSquareRoot_orthonormal
    (u : A) (hu : u ≠ 0) :
    (activityGramInverseSquareRoot (n := n) u hu)ᵀ *
      ((activityBasisMatrix (A := A) (n := n))ᵀ *
        activityBasisMatrix (A := A) (n := n)) *
        activityGramInverseSquareRoot (n := n) u hu = 1 := by
  let G := (activityBasisMatrix (A := A) (n := n))ᵀ *
    activityBasisMatrix (A := A) (n := n)
  let hG : G.PosDef := activityBasisMatrix_gram_posDef u hu
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

open scoped Matrix.Norms.L2Operator in
/-- The square of the two-norm of the orthonormalizing matrix equals the
two-norm of the inverse Gram matrix. -/
theorem activityGramInverseSquareRoot_twoNorm_sq
    (u : A) (hu : u ≠ 0) :
    ‖activityGramInverseSquareRoot (n := n) u hu‖ ^ 2 =
      ‖(((activityBasisMatrix (A := A) (n := n))ᵀ *
        activityBasisMatrix (A := A) (n := n))⁻¹)‖ := by
  let G := (activityBasisMatrix (A := A) (n := n))ᵀ *
    activityBasisMatrix (A := A) (n := n)
  let hG : G.PosDef := activityBasisMatrix_gram_posDef u hu
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

/-- The orthonormalizing inverse square root is symmetric. -/
theorem activityGramInverseSquareRoot_transpose
    (u : A) (hu : u ≠ 0) :
    (activityGramInverseSquareRoot (n := n) u hu)ᵀ =
      activityGramInverseSquareRoot (n := n) u hu := by
  let hG := activityBasisMatrix_gram_posDef (n := n) u hu
  have hHtranspose : (hG.posSemidef.sqrt)ᵀ = hG.posSemidef.sqrt := by
    simpa [Matrix.conjTranspose] using hG.posSemidef.posSemidef_sqrt.1.eq
  change (hG.posSemidef.sqrt⁻¹)ᵀ = hG.posSemidef.sqrt⁻¹
  rw [Matrix.transpose_nonsing_inv, hHtranspose]

/-- Its square is the inverse activity Gram matrix. -/
theorem activityGramInverseSquareRoot_mul_self
    (u : A) (hu : u ≠ 0) :
    activityGramInverseSquareRoot (n := n) u hu *
      activityGramInverseSquareRoot (n := n) u hu =
        (((activityBasisMatrix (A := A) (n := n))ᵀ *
          activityBasisMatrix (A := A) (n := n))⁻¹) := by
  let hG := activityBasisMatrix_gram_posDef (n := n) u hu
  change hG.posSemidef.sqrt⁻¹ * hG.posSemidef.sqrt⁻¹ = _
  rw [← Matrix.mul_inv_rev, hG.posSemidef.sqrt_mul_self]

/-- The paper's orthonormalized activity-basis matrix `C = B R`. -/
noncomputable def activityOrthonormalBasisMatrix
    (u : A) (hu : u ≠ 0) :
    Matrix (State A n) (Fin n → Bool) ℝ :=
  activityBasisMatrix (A := A) (n := n) *
    activityGramInverseSquareRoot (n := n) u hu

/-- The columns of `C = B R` are orthonormal. -/
theorem activityOrthonormalBasisMatrix_orthonormal
    (u : A) (hu : u ≠ 0) :
    (activityOrthonormalBasisMatrix (n := n) u hu)ᵀ *
      activityOrthonormalBasisMatrix (n := n) u hu = 1 := by
  simpa [activityOrthonormalBasisMatrix, Matrix.transpose_mul,
    Matrix.mul_assoc] using
      activityGramInverseSquareRoot_orthonormal (n := n) u hu

/-- Multiplication by the orthonormalized activity matrix preserves
Euclidean length of coefficient vectors. -/
theorem activityOrthonormalBasisMatrix_mulVec_norm
    (u : A) (hu : u ≠ 0) (c : (Fin n → Bool) → ℝ) :
    ‖WithLp.toLp 2
      ((activityOrthonormalBasisMatrix (n := n) u hu) *ᵥ c)‖ =
      ‖WithLp.toLp 2 c‖ := by
  let C := activityOrthonormalBasisMatrix (n := n) u hu
  have hdot : c ⬝ᵥ (Cᵀ *ᵥ (C *ᵥ c)) =
      (C *ᵥ c) ⬝ᵥ (C *ᵥ c) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hself : (C *ᵥ c) ⬝ᵥ (C *ᵥ c) = c ⬝ᵥ c := by
    calc
      (C *ᵥ c) ⬝ᵥ (C *ᵥ c) = c ⬝ᵥ (Cᵀ *ᵥ (C *ᵥ c)) := hdot.symm
      _ = c ⬝ᵥ ((Cᵀ * C) *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = c ⬝ᵥ c := by rw [activityOrthonormalBasisMatrix_orthonormal u hu,
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

open scoped Matrix.Norms.L2Operator in
/-- Gram conversion for a general real difference-distribution matrix:
the matrix of its compression in the orthonormal activity basis is bounded by
the inverse Gram norm times the paper's raw `Bᵀ M B` norm. -/
theorem activityOrthonormalBasisMatrix_compression_twoNorm_le
    (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖(activityOrthonormalBasisMatrix (n := n) u hu)ᵀ * M *
      activityOrthonormalBasisMatrix (n := n) u hu‖ ≤
      ‖(((activityBasisMatrix (A := A) (n := n))ᵀ *
        activityBasisMatrix (A := A) (n := n))⁻¹)‖ *
        ‖(activityBasisMatrix (A := A) (n := n))ᵀ * M *
          activityBasisMatrix (A := A) (n := n)‖ := by
  let B := activityBasisMatrix (A := A) (n := n)
  let R := activityGramInverseSquareRoot (n := n) u hu
  let Δ := Bᵀ * M * B
  have hRnorm : ‖R‖ ^ 2 = ‖(Bᵀ * B)⁻¹‖ :=
    activityGramInverseSquareRoot_twoNorm_sq (n := n) u hu
  have hRt : ‖Rᵀ‖ = ‖R‖ := by
    simpa [Matrix.conjTranspose] using Matrix.l2_opNorm_conjTranspose R
  have hmatrix : (B * R)ᵀ * M * (B * R) = Rᵀ * Δ * R := by
    simp [Δ, Matrix.transpose_mul, Matrix.mul_assoc]
  change ‖(B * R)ᵀ * M * (B * R)‖ ≤ ‖(Bᵀ * B)⁻¹‖ * ‖Δ‖
  rw [hmatrix]
  calc
    ‖Rᵀ * Δ * R‖ ≤ ‖Rᵀ * Δ‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Rᵀ‖ * ‖Δ‖) * ‖R‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖(Bᵀ * B)⁻¹‖ * ‖Δ‖ := by rw [hRt, ← hRnorm]; ring

/-- The normalized columns of the paper's matrix `B` span exactly the
activity subspace `V`. -/
theorem activitySubspace_eq_span_normalized :
    activitySubspace (A := A) (n := n) =
      Submodule.span ℝ
        (Set.range (normalizedActivityBoxIndicator (A := A) (n := n))) := by
  let W := Submodule.span ℝ
    (Set.range (normalizedActivityBoxIndicator (A := A) (n := n)))
  have hq (z : Fin n → Bool) :
      Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight z) ≠ 0 := by
    have hcard : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩)
    exact ne_of_gt (Real.sqrt_pos.2 (pow_pos hcard _))
  apply le_antisymm
  · rw [activitySubspace]
    apply Submodule.span_le.mpr
    rintro v ⟨z, rfl⟩
    have hz : normalizedActivityBoxIndicator (A := A) z ∈ W :=
      Submodule.subset_span ⟨z, rfl⟩
    convert W.smul_mem (Real.sqrt ((Fintype.card A : ℝ) ^ activityWeight z)) hz using 1
    simp [normalizedActivityBoxIndicator, smul_smul, hq]
  · apply Submodule.span_le.mpr
    rintro v ⟨z, rfl⟩
    exact (activitySubspace (A := A) (n := n)).smul_mem _
      (activityBoxIndicator_mem_activitySubspace z)

/-- Equivalently, `V` is the range of matrix multiplication by `B`.
This is the surjectivity needed for the paper's projection-coordinate formula. -/
theorem activitySubspace_eq_range_activityBasisMatrix :
    activitySubspace (A := A) (n := n) =
      LinearMap.range (activityBasisMatrix (A := A) (n := n)).mulVecLin := by
  rw [activitySubspace_eq_span_normalized, Matrix.range_mulVecLin]
  rfl

/-- The orthonormalized activity columns still span the paper's subspace
`V`, since the inverse square root `R` is invertible. -/
theorem activityOrthonormalBasisMatrix_mulVec_surjective_onto_V
    (u : A) (hu : u ≠ 0)
    (v : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n)) :
    ∃ c : (Fin n → Bool) → ℝ,
      activityOrthonormalBasisMatrix (n := n) u hu *ᵥ c = v := by
  let B := activityBasisMatrix (A := A) (n := n)
  let G := Bᵀ * B
  let hG : G.PosDef := activityBasisMatrix_gram_posDef u hu
  let H := hG.posSemidef.sqrt
  let R := H⁻¹
  have hHunit : IsUnit H := hG.posDef_sqrt.isUnit
  have hRunit : IsUnit R := Matrix.isUnit_nonsing_inv_iff.mpr hHunit
  have hRsurj : Function.Surjective R.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hRunit
  rw [activitySubspace_eq_range_activityBasisMatrix] at hv
  obtain ⟨d, hd⟩ := hv
  have hd0 : B *ᵥ d = v := hd
  obtain ⟨c, hc⟩ := hRsurj d
  refine ⟨c, ?_⟩
  change (B * R) *ᵥ c = v
  rw [← Matrix.mulVec_mulVec, hc]
  exact hd0

/-- Coordinates of the orthogonal projection onto `V` in the paper's
normalized activity-box basis. This is the projection formula
`B (Bᵀ B)⁻¹ Bᵀ` used before the truncated-differential estimate. -/
theorem activityOrthogonalProjection_coordinates
    (u : A) (hu : u ≠ 0) (v : State A n → ℝ) :
    (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
        (((activityOrthogonalProjection (A := A) (n := n)
          (WithLp.toLp 2 v)) : activityHilbertSubspace (A := A) (n := n)) :
          EuclideanSpace ℝ (State A n)) =
      (activityBasisMatrix (A := A) (n := n)) *ᵥ
        (((activityBasisMatrix (A := A) (n := n))ᵀ *
          activityBasisMatrix (A := A) (n := n))⁻¹ *ᵥ
            ((activityBasisMatrix (A := A) (n := n))ᵀ *ᵥ v)) := by
  let B := activityBasisMatrix (A := A) (n := n)
  let G := Bᵀ * B
  let pHilbert := activityOrthogonalProjection (A := A) (n := n)
    (WithLp.toLp 2 v)
  let p := (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
    (pHilbert : EuclideanSpace ℝ (State A n))
  have hp : p ∈ activitySubspace (A := A) (n := n) :=
    (mem_activityHilbertSubspace_iff
      (pHilbert : EuclideanSpace ℝ (State A n))).mp pHilbert.property
  rw [activitySubspace_eq_range_activityBasisMatrix] at hp
  obtain ⟨c, hc⟩ := hp
  have hc0 : B *ᵥ c = p := hc
  have hpair (z : Fin n → Bool) :
      (B.col z) ⬝ᵥ p = (B.col z) ⬝ᵥ v := by
    have hz' : normalizedActivityBoxIndicator (A := A) z ∈
        activitySubspace (A := A) (n := n) := by
      rw [activitySubspace_eq_span_normalized]
      exact Submodule.subset_span ⟨z, rfl⟩
    have hz : (WithLp.toLp 2 (B.col z) : EuclideanSpace ℝ (State A n)) ∈
        activityHilbertSubspace (A := A) (n := n) := by
      rw [mem_activityHilbertSubspace_iff]
      simpa only [B, activityBasisMatrix, Matrix.col_apply,
        WithLp.linearEquiv_apply] using hz'
    let bz : activityHilbertSubspace (A := A) (n := n) :=
      ⟨WithLp.toLp 2 (B.col z), hz⟩
    have hi := (activityHilbertSubspace (A := A) (n := n))
      |>.inner_orthogonalProjection_eq_of_mem_left bz (WithLp.toLp 2 v)
    rw [Submodule.coe_inner] at hi
    rw [euclidean_inner_eq_dotProduct, euclidean_inner_eq_dotProduct] at hi
    change (B.col z) ⬝ᵥ p = (B.col z) ⬝ᵥ v at hi
    exact hi
  have hnormal : Bᵀ *ᵥ p = Bᵀ *ᵥ v := by
    funext z
    change (B.col z) ⬝ᵥ p = (B.col z) ⬝ᵥ v
    exact hpair z
  have hdet : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det G).mp (activityBasisMatrix_gram_isUnit u hu)
  have hGc : G *ᵥ c = Bᵀ *ᵥ v := by
    calc
      G *ᵥ c = Bᵀ *ᵥ (B *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = Bᵀ *ᵥ p := by rw [hc0]
      _ = Bᵀ *ᵥ v := hnormal
  have hc' : c = G⁻¹ *ᵥ (Bᵀ *ᵥ v) := by
    rw [← hGc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hdet,
      Matrix.one_mulVec]
  change p = B *ᵥ (G⁻¹ *ᵥ (Bᵀ *ᵥ v))
  rw [← hc']
  exact hc0.symm

/-- A vector of `V` specified by its coordinates in the normalized
activity-box basis `B`. -/
noncomputable def activityBasisVector (c : (Fin n → Bool) → ℝ) :
    activityHilbertSubspace (A := A) (n := n) := by
  refine ⟨WithLp.toLp 2 ((activityBasisMatrix (A := A) (n := n)) *ᵥ c), ?_⟩
  rw [mem_activityHilbertSubspace_iff,
    activitySubspace_eq_range_activityBasisMatrix]
  exact ⟨c, rfl⟩

/-- The paper's matrix representation of the truncated-differential
operator `π_V M i_V` in the normalized activity-box basis is
`(Bᵀ B)⁻¹ Bᵀ M B`. -/
theorem activityTruncatedOperator_basisVector
    (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ)
    (c : (Fin n → Bool) → ℝ) :
    activityTruncatedOperator (A := A) (n := n) M
        (activityBasisVector (A := A) (n := n) c) =
      activityBasisVector (A := A) (n := n)
        (((((activityBasisMatrix (A := A) (n := n))ᵀ *
            activityBasisMatrix (A := A) (n := n))⁻¹ *
          ((activityBasisMatrix (A := A) (n := n))ᵀ * M *
            activityBasisMatrix (A := A) (n := n))) *ᵥ c)) := by
  let B := activityBasisMatrix (A := A) (n := n)
  let G := Bᵀ * B
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
  change (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
      (((activityOrthogonalProjection (A := A) (n := n)
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
          (WithLp.toLp 2 (B *ᵥ c)))) :
        activityHilbertSubspace (A := A) (n := n)) :
          EuclideanSpace ℝ (State A n)) =
    B *ᵥ ((G⁻¹ * (Bᵀ * M * B)) *ᵥ c)
  rw [Matrix.toEuclideanCLM_toLp]
  rw [activityOrthogonalProjection_coordinates u hu]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rfl

/-- A vector of `V` in the orthonormalized activity coordinates. -/
noncomputable def activityOrthonormalBasisVector
    (u : A) (hu : u ≠ 0) (c : (Fin n → Bool) → ℝ) :
    activityHilbertSubspace (A := A) (n := n) :=
  activityBasisVector (A := A) (n := n)
    (activityGramInverseSquareRoot (n := n) u hu *ᵥ c)

theorem activityOrthonormalBasisVector_norm
    (u : A) (hu : u ≠ 0) (c : (Fin n → Bool) → ℝ) :
    ‖activityOrthonormalBasisVector (n := n) u hu c‖ =
      ‖WithLp.toLp 2 c‖ := by
  change ‖WithLp.toLp 2
    (activityBasisMatrix (A := A) (n := n) *ᵥ
      (activityGramInverseSquareRoot (n := n) u hu *ᵥ c))‖ = _
  rw [Matrix.mulVec_mulVec]
  exact activityOrthonormalBasisMatrix_mulVec_norm u hu c

/-- The matrix of the truncated operator in orthonormal activity coordinates
is the compression `Cᵀ M C`. This converts the paper's matrix estimate into
an estimate of the actual operator on `V`. -/
theorem activityTruncatedOperator_orthonormalBasisVector
    (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ)
    (c : (Fin n → Bool) → ℝ) :
    activityTruncatedOperator (A := A) (n := n) M
        (activityOrthonormalBasisVector (n := n) u hu c) =
      activityOrthonormalBasisVector (n := n) u hu
        (((activityOrthonormalBasisMatrix (n := n) u hu)ᵀ * M *
          activityOrthonormalBasisMatrix (n := n) u hu) *ᵥ c) := by
  let B := activityBasisMatrix (A := A) (n := n)
  let R := activityGramInverseSquareRoot (n := n) u hu
  let Δ := Bᵀ * M * B
  have hR : R * R = (Bᵀ * B)⁻¹ :=
    activityGramInverseSquareRoot_mul_self (n := n) u hu
  have hRt : Rᵀ = R :=
    activityGramInverseSquareRoot_transpose (n := n) u hu
  have hcoord : (Bᵀ * B)⁻¹ * Δ * R = R * (Rᵀ * Δ * R) := by
    rw [← hR, hRt]
    simp only [Matrix.mul_assoc]
  change activityTruncatedOperator (A := A) (n := n) M
      (activityBasisVector (A := A) (n := n) (R *ᵥ c)) =
    activityBasisVector (A := A) (n := n)
      (R *ᵥ (((B * R)ᵀ * M * (B * R)) *ᵥ c))
  rw [activityTruncatedOperator_basisVector u hu]
  have hcompression : (B * R)ᵀ * M * (B * R) = Rᵀ * Δ * R := by
    simp [Δ, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hcompression]
  simp only [Matrix.mulVec_mulVec]
  simpa only [Δ, Matrix.mul_assoc] using
    congrArg (fun X : Matrix (Fin n → Bool) (Fin n → Bool) ℝ =>
      activityBasisVector (A := A) (n := n) (X *ᵥ c)) hcoord

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of the paper's truncated-differential operator is
bounded by the spectral norm of its orthonormal activity-coordinate matrix. -/
theorem activityTruncatedOperator_norm_le_compression
    (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖activityTruncatedOperator (A := A) (n := n) M‖ ≤
      ‖(activityOrthonormalBasisMatrix (n := n) u hu)ᵀ * M *
        activityOrthonormalBasisMatrix (n := n) u hu‖ := by
  let C := activityOrthonormalBasisMatrix (n := n) u hu
  let K := Cᵀ * M * C
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
  intro v
  obtain ⟨c, hc⟩ :=
    activityOrthonormalBasisMatrix_mulVec_surjective_onto_V u hu
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ))
        (v : EuclideanSpace ℝ (State A n)))
      ((mem_activityHilbertSubspace_iff
        (v : EuclideanSpace ℝ (State A n))).mp v.property)
  have hv : v = activityOrthonormalBasisVector (n := n) u hu c := by
    apply Subtype.ext
    apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
    change (WithLp.linearEquiv 2 ℝ (State A n → ℝ))
        (v : EuclideanSpace ℝ (State A n)) =
      activityBasisMatrix (A := A) (n := n) *ᵥ
        (activityGramInverseSquareRoot (n := n) u hu *ᵥ c)
    rw [Matrix.mulVec_mulVec]
    exact hc.symm
  rw [hv, activityTruncatedOperator_orthonormalBasisVector u hu M c,
    activityOrthonormalBasisVector_norm,
    activityOrthonormalBasisVector_norm]
  exact Matrix.l2_opNorm_mulVec K (WithLp.toLp 2 c)

/-- Algebraic description of the paper's orthogonal complement `V^⊥`, using
the Euclidean dot product on difference vectors. -/
def InActivityOrthogonalComplement (w : State A n → ℝ) : Prop :=
  ∀ v ∈ activitySubspace (A := A) (n := n), v ⬝ᵥ w = 0

/-- The algebraic dot-product definition of the paper's `V⊥` agrees with
the orthogonal complement of the Euclidean activity subspace. -/
theorem inActivityOrthogonalComplement_iff_mem_orthogonal
    (w : EuclideanSpace ℝ (State A n)) :
    InActivityOrthogonalComplement
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w) ↔
      w ∈ (activityHilbertSubspace (A := A) (n := n))ᗮ := by
  constructor
  · intro hw
    apply ((activityHilbertSubspace (A := A) (n := n)).mem_orthogonal' w).2
    intro v hv
    rw [euclidean_inner_eq_dotProduct, dotProduct_comm]
    exact hw _ ((mem_activityHilbertSubspace_iff v).mp hv)
  · intro hw v hv
    have hv' : WithLp.toLp 2 v ∈
        activityHilbertSubspace (A := A) (n := n) :=
      (mem_activityHilbertSubspace_iff (WithLp.toLp 2 v)).2 (by simpa using hv)
    have hpair :=
      ((activityHilbertSubspace (A := A) (n := n)).mem_orthogonal' w).1 hw
        (WithLp.toLp 2 v) hv'
    rw [euclidean_inner_eq_dotProduct] at hpair
    change ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w) ⬝ᵥ v = 0 at hpair
    rwa [dotProduct_comm] at hpair

/-- The uniform difference-distribution matrix vanishes on `V⊥`, as used
at the start of the paper's spectral-term analysis. -/
theorem uniformDifferenceDistributionMatrix_mulVec_eq_zero_of_activityOrthogonal
    (w : State A n → ℝ) (hw : InActivityOrthogonalComplement w) :
    uniformDifferenceDistributionMatrix (State A n) *ᵥ w = 0 := by
  classical
  let z₀ : Fin n → Bool := fun _ => false
  let z₁ : Fin n → Bool := fun _ => true
  have hzero : w 0 = 0 := by
    have hp := hw (activityBoxIndicator (A := A) z₀)
      (activityBoxIndicator_mem_activitySubspace z₀)
    have hfun (x : State A n) : (∀ i, x i = 0) ↔ x = 0 := by
      simp [funext_iff]
    have hpair : (∑ x : State A n,
        if (∀ i, x i = 0) then w x else 0) = 0 := by
      simpa [z₀, activityBoxIndicator, InActivityBox, dotProduct] using hp
    have hpair' : (∑ x : State A n,
        if x = 0 then w x else 0) = 0 := by
      simpa only [hfun] using hpair
    simpa using hpair'
  have hsum : (∑ a : State A n, w a) = 0 := by
    have hp := hw (activityBoxIndicator (A := A) z₁)
      (activityBoxIndicator_mem_activitySubspace z₁)
    simpa [z₁, activityBoxIndicator, InActivityBox, dotProduct] using hp
  have hsum' : (∑ a : State A n, if a = 0 then (0 : ℝ) else w a) = 0 := by
    have hpartition : (∑ a : State A n, w a) =
        (∑ a : State A n, if a = 0 then w a else 0) +
          (∑ a : State A n, if a = 0 then 0 else w a) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    have hfirst : (∑ a : State A n, if a = 0 then w a else 0) = 0 := by
      simp [hzero]
    rw [hfirst] at hpartition
    linarith
  funext b
  by_cases hb : b = 0
  · subst b
    simp [Matrix.mulVec, dotProduct,
      uniformDifferenceDistributionMatrix_apply, hzero]
  · simp only [Pi.zero_apply, Matrix.mulVec, dotProduct,
      uniformDifferenceDistributionMatrix_apply, if_neg hb]
    calc
      (∑ a : State A n,
        (if a = 0 then (0 : ℝ)
          else 1 / ((Fintype.card (State A n) - 1 : ℕ) : ℝ)) * w a) =
          (1 / ((Fintype.card (State A n) - 1 : ℕ) : ℝ)) *
            (∑ a : State A n, if a = 0 then 0 else w a) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              by_cases ha : a = 0 <;> simp [ha]
      _ = 0 := by rw [hsum', mul_zero]

/-- Euclidean form of the paper's observation `V⊥ ⊆ ker U`. -/
theorem uniformDifferenceDistributionMatrix_toEuclideanCLM_eq_zero_of_mem_orthogonal
    (w : EuclideanSpace ℝ (State A n))
    (hw : w ∈ (activityHilbertSubspace (A := A) (n := n))ᗮ) :
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (uniformDifferenceDistributionMatrix (State A n)) w = 0 := by
  apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
  change uniformDifferenceDistributionMatrix (State A n) *ᵥ
    ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w) = 0
  exact uniformDifferenceDistributionMatrix_mulVec_eq_zero_of_activityOrthogonal
    _ ((inActivityOrthogonalComplement_iff_mem_orthogonal w).2 hw)

/-- The image of the uniform difference-distribution matrix lies in `V`.
This follows from symmetry and its vanishing on `V⊥`. -/
theorem uniformDifferenceDistributionMatrix_toEuclideanCLM_mem_activityHilbertSubspace
    (v : EuclideanSpace ℝ (State A n)) :
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (uniformDifferenceDistributionMatrix (State A n)) v ∈
        activityHilbertSubspace (A := A) (n := n) := by
  let K := activityHilbertSubspace (A := A) (n := n)
  let U := uniformDifferenceDistributionMatrix (State A n)
  have hmem : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) U v ∈ Kᗮᗮ := by
    apply ((Kᗮ).mem_orthogonal'
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) U v)).2
    intro w hw
    rw [euclidean_inner_eq_dotProduct]
    change (U *ᵥ ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) v)) ⬝ᵥ
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w) = 0
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      uniformDifferenceDistributionMatrix_transpose]
    have hzero := uniformDifferenceDistributionMatrix_mulVec_eq_zero_of_activityOrthogonal
      ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) w)
      ((inActivityOrthogonalComplement_iff_mem_orthogonal w).2 hw)
    rw [hzero]
    simp
  simpa only [K.orthogonal_orthogonal] using hmem

/-- The paper's mixed block `π_V M i_{V⊥}`. -/
noncomputable def activityComplementToActivityOperator
    (M : Matrix (State A n) (State A n) ℝ) :
    (activityHilbertSubspace (A := A) (n := n))ᗮ →L[ℝ]
      activityHilbertSubspace (A := A) (n := n) :=
  (activityHilbertSubspace (A := A) (n := n)).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
      ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL

/-- The paper's mixed block `π_{V⊥} M i_V`. -/
noncomputable def activityToComplementOperator
    (M : Matrix (State A n) (State A n) ℝ) :
    activityHilbertSubspace (A := A) (n := n) →L[ℝ]
      (activityHilbertSubspace (A := A) (n := n))ᗮ :=
  ((activityHilbertSubspace (A := A) (n := n))ᗮ).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
      (activityHilbertSubspace (A := A) (n := n)).subtypeL

/-- The paper's spectral block `π_{V⊥} M i_{V⊥}`. -/
noncomputable def activityComplementOperator
    (M : Matrix (State A n) (State A n) ℝ) :
    (activityHilbertSubspace (A := A) (n := n))ᗮ →L[ℝ]
      (activityHilbertSubspace (A := A) (n := n))ᗮ :=
  ((activityHilbertSubspace (A := A) (n := n))ᗮ).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M ∘L
      ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL

/-- The uniform benchmark disappears from the mixed block with input in
`V⊥`, exactly as in the paper's spectral-term setup. -/
theorem activityComplementToActivityOperator_sub_uniform
    (M : Matrix (State A n) (State A n) ℝ) :
    activityComplementToActivityOperator
      (M - uniformDifferenceDistributionMatrix (State A n)) =
        activityComplementToActivityOperator M := by
  apply ContinuousLinearMap.ext
  intro v
  change (activityHilbertSubspace (A := A) (n := n)).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (M - uniformDifferenceDistributionMatrix (State A n))
        (v : EuclideanSpace ℝ (State A n))) =
    (activityHilbertSubspace (A := A) (n := n)).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
        (v : EuclideanSpace ℝ (State A n)))
  rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
    uniformDifferenceDistributionMatrix_toEuclideanCLM_eq_zero_of_mem_orthogonal
      (v : EuclideanSpace ℝ (State A n)) v.property, sub_zero]

/-- The uniform benchmark also disappears from the `V⊥`-to-`V⊥` block. -/
theorem activityComplementOperator_sub_uniform
    (M : Matrix (State A n) (State A n) ℝ) :
    activityComplementOperator
      (M - uniformDifferenceDistributionMatrix (State A n)) =
        activityComplementOperator M := by
  apply ContinuousLinearMap.ext
  intro v
  change ((activityHilbertSubspace (A := A) (n := n))ᗮ).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (M - uniformDifferenceDistributionMatrix (State A n))
        (v : EuclideanSpace ℝ (State A n))) =
    ((activityHilbertSubspace (A := A) (n := n))ᗮ).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
        (v : EuclideanSpace ℝ (State A n)))
  rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
    uniformDifferenceDistributionMatrix_toEuclideanCLM_eq_zero_of_mem_orthogonal
      (v : EuclideanSpace ℝ (State A n)) v.property, sub_zero]

/-- The uniform benchmark has image in `V`, so its projection to `V⊥`
vanishes also on inputs from `V`. -/
theorem activityToComplementOperator_sub_uniform
    (M : Matrix (State A n) (State A n) ℝ) :
    activityToComplementOperator
      (M - uniformDifferenceDistributionMatrix (State A n)) =
        activityToComplementOperator M := by
  let K := activityHilbertSubspace (A := A) (n := n)
  let U := uniformDifferenceDistributionMatrix (State A n)
  apply ContinuousLinearMap.ext
  intro v
  have hUv : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) U
      (v : EuclideanSpace ℝ (State A n)) ∈ K :=
    uniformDifferenceDistributionMatrix_toEuclideanCLM_mem_activityHilbertSubspace _
  have hzero : (Kᗮ).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) U
        (v : EuclideanSpace ℝ (State A n))) = 0 :=
    (Kᗮ).orthogonalProjection_eq_zero_iff.2 (K.le_orthogonal_orthogonal hUv)
  change (Kᗮ).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) (M - U)
        (v : EuclideanSpace ℝ (State A n))) =
    (Kᗮ).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
        (v : EuclideanSpace ℝ (State A n)))
  rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
    map_sub, hzero, sub_zero]

open scoped Matrix.Norms.L2Operator in
/-- Two-coordinate Cauchy-Schwarz, used for the paper's four-block norm
inequality. -/
private theorem twoTermCauchy_sq (a b p q : ℝ) :
    (p * a + q * b) ^ 2 ≤
      (p ^ 2 + q ^ 2) * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (p * b - q * a)]

/-- Scalar inequality for a two-by-two matrix acting on two component
lengths. -/
private theorem fourBlockScalarBound
    (a b c d p q r s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h₀ : c ≤ p * a + q * b) (h₁ : d ≤ r * a + s * b) :
    c ^ 2 + d ^ 2 ≤
      (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) := by
  have hpa : 0 ≤ p * a + q * b :=
    add_nonneg (mul_nonneg hp ha) (mul_nonneg hq hb)
  have hrb : 0 ≤ r * a + s * b :=
    add_nonneg (mul_nonneg hr ha) (mul_nonneg hs hb)
  calc
    c ^ 2 + d ^ 2 ≤ (p * a + q * b) ^ 2 +
        (r * a + s * b) ^ 2 :=
      add_le_add ((sq_le_sq₀ hc hpa).2 h₀) ((sq_le_sq₀ hd hrb).2 h₁)
    _ ≤ (p ^ 2 + q ^ 2) * (a ^ 2 + b ^ 2) +
        (r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) :=
      add_le_add (twoTermCauchy_sq a b p q) (twoTermCauchy_sq a b r s)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
open scoped Matrix.Norms.L2Operator in
/-- The paper's four-block norm inequality for the orthogonal decomposition
`V ⊕ V⊥`. This is the linear-algebra step joining the truncated estimate to
the three spectral terms in Theorem 3. The paper invokes its general block
matrix lemma; here the two-coordinate Cauchy-Schwarz inequality proves this
special case directly. -/
theorem activity_fourBlock_norm_sq_le
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖M‖ ^ 2 ≤
      ‖activityTruncatedOperator M‖ ^ 2 +
      ‖activityComplementToActivityOperator M‖ ^ 2 +
      ‖activityToComplementOperator M‖ ^ 2 +
      ‖activityComplementOperator M‖ ^ 2 := by
  let K := activityHilbertSubspace (A := A) (n := n)
  let Q := Kᗮ
  let F := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
  let T₀₀ := activityTruncatedOperator (A := A) (n := n) M
  let T₀₁ := activityComplementToActivityOperator (A := A) (n := n) M
  let T₁₀ := activityToComplementOperator (A := A) (n := n) M
  let T₁₁ := activityComplementOperator (A := A) (n := n) M
  let R : ℝ := ‖T₀₀‖ ^ 2 + ‖T₀₁‖ ^ 2 + ‖T₁₀‖ ^ 2 + ‖T₁₁‖ ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrow₀ (x : EuclideanSpace ℝ (State A n)) :
      ‖K.orthogonalProjection (F x)‖ ≤
        ‖T₀₀‖ * ‖K.orthogonalProjection x‖ +
        ‖T₀₁‖ * ‖Q.orthogonalProjection x‖ := by
    have hdecomp : K.orthogonalProjection (F x) =
        T₀₀ (K.orthogonalProjection x) +
          T₀₁ (Q.orthogonalProjection x) := by
      change K.orthogonalProjection (F x) =
        K.orthogonalProjection (F (K.orthogonalProjection x)) +
          K.orthogonalProjection (F (Q.orthogonalProjection x))
      have hsplit : (K.orthogonalProjection x : EuclideanSpace ℝ (State A n)) +
          (Q.orthogonalProjection x : EuclideanSpace ℝ (State A n)) = x := by
        simpa only [Q] using K.starProjection_add_starProjection_orthogonal x
      rw [← map_add, ← map_add, hsplit]
    rw [hdecomp]
    exact (norm_add_le _ _).trans
      (add_le_add (ContinuousLinearMap.le_opNorm T₀₀ _)
        (ContinuousLinearMap.le_opNorm T₀₁ _))
  have hrow₁ (x : EuclideanSpace ℝ (State A n)) :
      ‖Q.orthogonalProjection (F x)‖ ≤
        ‖T₁₀‖ * ‖K.orthogonalProjection x‖ +
        ‖T₁₁‖ * ‖Q.orthogonalProjection x‖ := by
    have hdecomp : Q.orthogonalProjection (F x) =
        T₁₀ (K.orthogonalProjection x) +
          T₁₁ (Q.orthogonalProjection x) := by
      change Q.orthogonalProjection (F x) =
        Q.orthogonalProjection (F (K.orthogonalProjection x)) +
          Q.orthogonalProjection (F (Q.orthogonalProjection x))
      have hsplit : (K.orthogonalProjection x : EuclideanSpace ℝ (State A n)) +
          (Q.orthogonalProjection x : EuclideanSpace ℝ (State A n)) = x := by
        simpa only [Q] using K.starProjection_add_starProjection_orthogonal x
      rw [← map_add, ← map_add, hsplit]
    rw [hdecomp]
    exact (norm_add_le _ _).trans
      (add_le_add (ContinuousLinearMap.le_opNorm T₁₀ _)
        (ContinuousLinearMap.le_opNorm T₁₁ _))
  have hpoint (x : EuclideanSpace ℝ (State A n)) :
      ‖F x‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
    let a := ‖K.orthogonalProjection x‖
    let b := ‖Q.orthogonalProjection x‖
    let c := ‖K.orthogonalProjection (F x)‖
    let d := ‖Q.orthogonalProjection (F x)‖
    let p := ‖T₀₀‖
    let q := ‖T₀₁‖
    let r := ‖T₁₀‖
    let s := ‖T₁₁‖
    have h₀ : c ≤ p * a + q * b := hrow₀ x
    have h₁ : d ≤ r * a + s * b := hrow₁ x
    have hx : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_projection x K
    have hy : ‖F x‖ ^ 2 = c ^ 2 + d ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_projection (F x) K
    have hscalar : c ^ 2 + d ^ 2 ≤
        (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) :=
      fourBlockScalarBound a b c d p q r s
        (norm_nonneg (K.orthogonalProjection x))
        (norm_nonneg (Q.orthogonalProjection x))
        (norm_nonneg (K.orthogonalProjection (F x)))
        (norm_nonneg (Q.orthogonalProjection (F x)))
        (norm_nonneg T₀₀) (norm_nonneg T₀₁)
        (norm_nonneg T₁₀) (norm_nonneg T₁₁) h₀ h₁
    calc
      ‖F x‖ ^ 2 = c ^ 2 + d ^ 2 := hy
      _ ≤ (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) := hscalar
      _ = R * ‖x‖ ^ 2 := by rw [hx]
  have hnorm : ‖M‖ ≤ Real.sqrt R := by
    rw [Matrix.cstar_norm_def]
    apply ContinuousLinearMap.opNorm_le_bound F (Real.sqrt_nonneg R)
    intro x
    calc
      ‖F x‖ = Real.sqrt (‖F x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (R * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hpoint x)
      _ = Real.sqrt R * ‖x‖ := by
        rw [Real.sqrt_mul hR, Real.sqrt_sq (norm_nonneg _)]
  have hsq := (sq_le_sq₀ (norm_nonneg M) (Real.sqrt_nonneg R)).2 hnorm
  rw [Real.sq_sqrt hR] at hsq
  exact hsq

set_option maxHeartbeats 800000 in
open scoped Matrix.Norms.L2Operator in
/-- The sharp two-by-two block comparison behind Theorem 4. The hypothesis
is the scalar quadratic bound for the matrix of four block norms, so it can
be checked independently of the underlying difference-distribution matrix. -/
theorem activity_fourBlock_norm_le_of_quadratic_bound
    (M : Matrix (State A n) (State A n) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hquad : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (‖activityTruncatedOperator M‖ * a +
        ‖activityComplementToActivityOperator M‖ * b) ^ 2 +
      (‖activityToComplementOperator M‖ * a +
        ‖activityComplementOperator M‖ * b) ^ 2 ≤
        t ^ 2 * (a ^ 2 + b ^ 2)) :
    ‖M‖ ≤ t := by
  let K := activityHilbertSubspace (A := A) (n := n)
  let Q := Kᗮ
  let F := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
  let T₀₀ := activityTruncatedOperator (A := A) (n := n) M
  let T₀₁ := activityComplementToActivityOperator (A := A) (n := n) M
  let T₁₀ := activityToComplementOperator (A := A) (n := n) M
  let T₁₁ := activityComplementOperator (A := A) (n := n) M
  have hrow₀ (x : EuclideanSpace ℝ (State A n)) :
      ‖K.orthogonalProjection (F x)‖ ≤
        ‖T₀₀‖ * ‖K.orthogonalProjection x‖ +
          ‖T₀₁‖ * ‖Q.orthogonalProjection x‖ := by
    have hdecomp : K.orthogonalProjection (F x) =
        T₀₀ (K.orthogonalProjection x) +
          T₀₁ (Q.orthogonalProjection x) := by
      change K.orthogonalProjection (F x) =
        K.orthogonalProjection (F (K.orthogonalProjection x)) +
          K.orthogonalProjection (F (Q.orthogonalProjection x))
      have hsplit : (K.orthogonalProjection x : EuclideanSpace ℝ (State A n)) +
          (Q.orthogonalProjection x : EuclideanSpace ℝ (State A n)) = x := by
        simpa only [Q] using K.starProjection_add_starProjection_orthogonal x
      rw [← map_add, ← map_add, hsplit]
    rw [hdecomp]
    exact (norm_add_le _ _).trans
      (add_le_add (ContinuousLinearMap.le_opNorm T₀₀ _)
        (ContinuousLinearMap.le_opNorm T₀₁ _))
  have hrow₁ (x : EuclideanSpace ℝ (State A n)) :
      ‖Q.orthogonalProjection (F x)‖ ≤
        ‖T₁₀‖ * ‖K.orthogonalProjection x‖ +
          ‖T₁₁‖ * ‖Q.orthogonalProjection x‖ := by
    have hdecomp : Q.orthogonalProjection (F x) =
        T₁₀ (K.orthogonalProjection x) +
          T₁₁ (Q.orthogonalProjection x) := by
      change Q.orthogonalProjection (F x) =
        Q.orthogonalProjection (F (K.orthogonalProjection x)) +
          Q.orthogonalProjection (F (Q.orthogonalProjection x))
      have hsplit : (K.orthogonalProjection x : EuclideanSpace ℝ (State A n)) +
          (Q.orthogonalProjection x : EuclideanSpace ℝ (State A n)) = x := by
        simpa only [Q] using K.starProjection_add_starProjection_orthogonal x
      rw [← map_add, ← map_add, hsplit]
    rw [hdecomp]
    exact (norm_add_le _ _).trans
      (add_le_add (ContinuousLinearMap.le_opNorm T₁₀ _)
        (ContinuousLinearMap.le_opNorm T₁₁ _))
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound F ht
  intro x
  let a := ‖K.orthogonalProjection x‖
  let b := ‖Q.orthogonalProjection x‖
  let c := ‖K.orthogonalProjection (F x)‖
  let d := ‖Q.orthogonalProjection (F x)‖
  have hc : c ≤ ‖T₀₀‖ * a + ‖T₀₁‖ * b := hrow₀ x
  have hd : d ≤ ‖T₁₀‖ * a + ‖T₁₁‖ * b := hrow₁ x
  have hright₀ : 0 ≤ ‖T₀₀‖ * a + ‖T₀₁‖ * b := by positivity
  have hright₁ : 0 ≤ ‖T₁₀‖ * a + ‖T₁₁‖ * b := by positivity
  have hx : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_projection x K
  have hy : ‖F x‖ ^ 2 = c ^ 2 + d ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_projection (F x) K
  have hsq : ‖F x‖ ^ 2 ≤ (t * ‖x‖) ^ 2 := by
    calc
      ‖F x‖ ^ 2 = c ^ 2 + d ^ 2 := hy
      _ ≤ (‖T₀₀‖ * a + ‖T₀₁‖ * b) ^ 2 +
          (‖T₁₀‖ * a + ‖T₁₁‖ * b) ^ 2 :=
        add_le_add ((sq_le_sq₀ (norm_nonneg _) hright₀).2 hc)
          ((sq_le_sq₀ (norm_nonneg _) hright₁).2 hd)
      _ ≤ t ^ 2 * (a ^ 2 + b ^ 2) :=
        hquad a b (norm_nonneg _) (norm_nonneg _)
      _ = (t * ‖x‖) ^ 2 := by rw [← hx, mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).1 hsq

/-- The paper's explicit `Δ = Bᵀ(D^L-U)B` coordinate, obtained by subtracting
its `mdslin` and `unilin` formulas. -/
theorem linear_centered_activityBasisMatrix_coordinate
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
      ((activityBasisMatrix (A := A) (n := n))ᵀ *
        (deterministicDifferenceDistributionMatrix
          (fun a : State A n => L a) -
          uniformDifferenceDistributionMatrix (State A n)) *
          activityBasisMatrix (A := A) (n := n)) y x =
      (if n + 1 ≤ activityWeight x + activityWeight y then
        (Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y - n)
      else 1) -
        (1 +
          (((Fintype.card A : ℝ) ^ activityWeight x - 1) *
            ((Fintype.card A : ℝ) ^ activityWeight y - 1)) /
              ((Fintype.card A : ℝ) ^ n - 1)) := by
  let B := activityBasisMatrix (A := A) (n := n)
  let DL := deterministicDifferenceDistributionMatrix
    (fun a : State A n => L a)
  let U := uniformDifferenceDistributionMatrix (State A n)
  have hmatrix : (Bᵀ * (DL - U) * B) y x =
      (Bᵀ * DL * B) y x - (Bᵀ * U * B) y x := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  change Real.sqrt ((Fintype.card A : ℝ) ^ (activityWeight x + activityWeight y)) *
    (Bᵀ * (DL - U) * B) y x = _
  rw [hmatrix, mul_sub,
    linear_activityBasisMatrix_coordinate L hMDS x y,
    uniform_activityBasisMatrix_coordinate (A := A) x y]

/-- The tensor-product kernel underlying the paper's normalized activity
Gram matrix. Its parameter is `1/√q` for an alphabet of size `q`. -/
def booleanActivityGramKernel (r : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  fun x y => ∏ i : Fin n, if x i = y i then 1 else r

/-- The tensor-product kernel is a power indexed by Hamming distance. -/
theorem booleanActivityGramKernel_coordinate (r : ℝ)
    (x y : Fin n → Bool) :
    booleanActivityGramKernel r x y =
      r ^ activityWeight (activityXor x y) := by
  have hw : activityWeight (activityXor x y) =
      ∑ i : Fin n, if x i = y i then 0 else 1 := by
    unfold activityWeight
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases hx : x i <;> cases hy : y i <;>
      simp [activityXor, hx, hy]
  rw [booleanActivityGramKernel, hw]
  have hterm (i : Fin n) :
      (if x i = y i then (1 : ℝ) else r) =
        r ^ (if x i = y i then 0 else 1) := by
    by_cases h : x i = y i <;> simp [h]
  simp_rw [hterm]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- The actual activity Gram matrix is the Boolean-cube tensor kernel at
`r = 1/√q`, exactly as in the paper. -/
theorem activityBasisMatrix_gram_eq_booleanKernel :
    (activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n) =
        booleanActivityGramKernel (n := n)
          (1 / Real.sqrt (Fintype.card A : ℝ)) := by
  let q : ℝ := Fintype.card A
  have hq : 0 ≤ q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_le (Fintype.card A))
  have hsqrtpow (m : ℕ) : Real.sqrt (q ^ m) = (Real.sqrt q) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hq m), ih, pow_succ]
  ext y x
  rw [activityBasisMatrix_gram_coordinate,
    booleanActivityGramKernel_coordinate]
  rw [hsqrtpow]
  have hxor : activityXor x y = activityXor y x := by
    funext i
    simp [activityXor, Bool.xor_comm]
  simp [q, one_div, inv_pow, hxor]

/-- A one-coordinate cancellation identity for the Gram kernel and its
candidate inverse. -/
private theorem booleanActivityGramKernel_single_sum
    (r : ℝ) (a b : Bool) :
    (∑ z : Bool,
      (if a = z then (1 : ℝ) else r) *
        (if z = b then (1 : ℝ) else -r)) =
      if a = b then 1 - r ^ 2 else 0 := by
  cases a <;> cases b <;> simp <;> ring

/-- Multiplying the Boolean-cube Gram kernel by the same kernel at `-r`
eliminates all off-diagonal entries. -/
theorem booleanActivityGramKernel_mul_negative (r : ℝ) :
    booleanActivityGramKernel (n := n) r *
      booleanActivityGramKernel (n := n) (-r) =
        (1 - r ^ 2) ^ n • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, booleanActivityGramKernel,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  calc
    (∑ z : Fin n → Bool,
      (∏ i : Fin n, if x i = z i then (1 : ℝ) else r) *
        (∏ i : Fin n, if z i = y i then (1 : ℝ) else -r)) =
      ∑ z : Fin n → Bool,
        ∏ i : Fin n,
          (if x i = z i then (1 : ℝ) else r) *
            (if z i = y i then (1 : ℝ) else -r) := by
              simp only [Finset.prod_mul_distrib]
    _ = ∏ i : Fin n,
          ∑ z : Bool,
            (if x i = z then (1 : ℝ) else r) *
              (if z = y i then (1 : ℝ) else -r) := by
          simpa using (Finset.sum_prod_piFinset (s := Finset.univ)
            (g := fun i z =>
              (if x i = z then (1 : ℝ) else r) *
                (if z = y i then (1 : ℝ) else -r)))
    _ = (1 - r ^ 2) ^ n * if x = y then 1 else 0 := by
      simp only [booleanActivityGramKernel_single_sum]
      by_cases hxy : x = y
      · subst y
        simp [Finset.prod_const]
      · have hbad : ∃ i : Fin n, x i ≠ y i := by
          by_contra h
          push_neg at h
          exact hxy (funext h)
        obtain ⟨i, hi⟩ := hbad
        simp only [if_neg hxy, mul_zero]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The exact inverse of the Boolean-cube Gram kernel, an algebraic form of
the paper's tensor-product calculation. -/
theorem booleanActivityGramKernel_inverse (r : ℝ)
    (hr : 1 - r ^ 2 ≠ 0) :
    (booleanActivityGramKernel (n := n) r)⁻¹ =
      ((1 - r ^ 2) ^ n)⁻¹ • booleanActivityGramKernel (n := n) (-r) := by
  have hright : booleanActivityGramKernel (n := n) r *
      (((1 - r ^ 2) ^ n)⁻¹ • booleanActivityGramKernel (n := n) (-r)) = 1 := by
    rw [Matrix.mul_smul, booleanActivityGramKernel_mul_negative]
    rw [smul_smul]
    simp [hr]
  exact Matrix.inv_eq_right_inv hright

/-- The inverse of the paper's actual activity Gram matrix has an explicit
tensor-product formula whenever the alphabet has at least two elements. -/
theorem activityBasisMatrix_gram_inverse
    (u : A) (hu : u ≠ 0) :
    (((activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n))⁻¹) =
      ((1 - (1 / Real.sqrt (Fintype.card A : ℝ)) ^ 2) ^ n)⁻¹ •
        booleanActivityGramKernel (n := n)
          (-(1 / Real.sqrt (Fintype.card A : ℝ))) := by
  let q : ℝ := Fintype.card A
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩
  have hq : (1 : ℝ) < q := by
    dsimp [q]
    exact_mod_cast hcard
  have hsqrt : 1 < Real.sqrt q := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hrpos : 0 < 1 / Real.sqrt q := by positivity
  have hrlt : 1 / Real.sqrt q < 1 :=
    (div_lt_iff₀ (by positivity : 0 < Real.sqrt q)).2 (by simpa using hsqrt)
  have hr : 1 - (1 / Real.sqrt q) ^ 2 ≠ 0 := by
    have hsq : (1 / Real.sqrt q) ^ 2 < 1 := by nlinarith
    exact ne_of_gt (sub_pos.mpr hsq)
  rw [activityBasisMatrix_gram_eq_booleanKernel]
  exact booleanActivityGramKernel_inverse (n := n) (1 / Real.sqrt q) hr

/-- The absolute row sum of the inverse kernel before its scalar factor.
This is the row-sum estimate used to control the inverse Gram norm. -/
theorem booleanActivityGramKernel_negative_rowAbsSum
    (r : ℝ) (hr : 0 ≤ r) (x : Fin n → Bool) :
    (∑ y : Fin n → Bool,
      |booleanActivityGramKernel (n := n) (-r) x y|) =
        (1 + r) ^ n := by
  have hentry (y : Fin n → Bool) :
      |booleanActivityGramKernel (n := n) (-r) x y| =
        booleanActivityGramKernel (n := n) r x y := by
    rw [booleanActivityGramKernel_coordinate,
      booleanActivityGramKernel_coordinate]
    simp [abs_pow, abs_neg, abs_of_nonneg hr]
  simp_rw [hentry]
  calc
    (∑ y : Fin n → Bool, booleanActivityGramKernel (n := n) r x y) =
        ∏ i : Fin n,
          ∑ b : Bool, if x i = b then (1 : ℝ) else r := by
        simpa only [booleanActivityGramKernel] using
          (Finset.sum_prod_piFinset (s := Finset.univ)
            (g := fun i b => if x i = b then (1 : ℝ) else r))
    _ = ∏ _i : Fin n, (1 + r) := by
      apply Finset.prod_congr rfl
      intro i _
      cases x i <;> simp [add_comm]
    _ = (1 + r) ^ n := by simp

/-- Translation by an activity pattern on the Boolean cube. It indexes the
permutation matrices in a convolution expansion of the Gram kernel. -/
def activityXorPermutation (z : Fin n → Bool) : Equiv.Perm (Fin n → Bool) where
  toFun x := activityXor x z
  invFun x := activityXor x z
  left_inv x := by
    funext i
    simp [activityXor]
  right_inv x := by
    funext i
    simp [activityXor]

/-- A Boolean-cube Gram-kernel entry is a weighted sum of entries of
activity-translation permutation matrices. -/
theorem booleanActivityGramKernel_eq_sum_permutations (r : ℝ) :
    booleanActivityGramKernel (n := n) r =
      ∑ z : Fin n → Bool,
        (r ^ activityWeight z) • (activityXorPermutation z).permMatrix ℝ := by
  classical
  ext x y
  rw [booleanActivityGramKernel_coordinate]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hperm (z : Fin n → Bool) :
      ((activityXorPermutation z).permMatrix ℝ) x y =
        if activityXorPermutation z x = y then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp_rw [hperm]
  have htarget : activityXorPermutation (activityXor x y) x = y := by
    funext i
    simp [activityXorPermutation, activityXor]
  rw [Finset.sum_eq_single (activityXor x y)]
  · simp [htarget]
  · intro z _ hne
    have hz : activityXorPermutation z x ≠ y := by
      intro h
      apply hne
      change activityXor x z = y at h
      calc
        z = activityXor x (activityXor x z) := by
          funext i
          simp [activityXor]
        _ = activityXor x y := congrArg (activityXor x) h
    simp [hz]
  · simp

open scoped Matrix.Norms.L2Operator in
/-- The two-norm of the Boolean-cube kernel is bounded by its absolute row
sum, using its expansion into norm-one permutation matrices.

**Deviation from the paper:** the paper bounds the Gram inverse through
eigenvalues of a tensor product of `2 × 2` matrices. This proof uses the
Boolean-cube translation-permutation expansion instead. -/
theorem booleanActivityGramKernel_negative_twoNorm_le
    (r : ℝ) (hr : 0 ≤ r) :
    ‖booleanActivityGramKernel (n := n) (-r)‖ ≤ (1 + r) ^ n := by
  rw [booleanActivityGramKernel_eq_sum_permutations]
  calc
    ‖∑ z : Fin n → Bool,
      ((-r) ^ activityWeight z) • (activityXorPermutation z).permMatrix ℝ‖ ≤
        ∑ z : Fin n → Bool,
          ‖((-r) ^ activityWeight z) •
            (activityXorPermutation z).permMatrix ℝ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z : Fin n → Bool, |(-r) ^ activityWeight z| := by
      apply Finset.sum_le_sum
      intro z _
      rw [norm_smul, Real.norm_eq_abs]
      have hperm := Matrix.permMatrix_l2_opNorm_le
        (𝕜 := ℝ) (activityXorPermutation z)
      nlinarith [abs_nonneg ((-r) ^ activityWeight z)]
    _ = (1 + r) ^ n := by
      have hentry (z : Fin n → Bool) :
          |(-r) ^ activityWeight z| =
            |booleanActivityGramKernel (n := n) (-r)
              (fun _ : Fin n => false) z| := by
        rw [booleanActivityGramKernel_coordinate]
        have hxor : activityXor (fun _ : Fin n => false) z = z := by
          funext i
          simp [activityXor]
        rw [hxor]
      simp_rw [hentry]
      exact booleanActivityGramKernel_negative_rowAbsSum r hr _

open scoped Matrix.Norms.L2Operator in
/-- The inverse Gram two-norm bound from the paper's tensor-product lemma:
`‖(BᵀB)⁻¹‖₂ ≤ (1 - 1/√q)⁻ⁿ`. -/
theorem activityBasisMatrix_gram_inverse_twoNorm_le
    (u : A) (hu : u ≠ 0) :
    ‖(((activityBasisMatrix (A := A) (n := n))ᵀ *
      activityBasisMatrix (A := A) (n := n))⁻¹)‖ ≤
      ((1 - 1 / Real.sqrt (Fintype.card A : ℝ)) ^ n)⁻¹ := by
  let r : ℝ := 1 / Real.sqrt (Fintype.card A : ℝ)
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, u, Ne.symm hu⟩
  have hq : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
  have hsqrt : 1 < Real.sqrt (Fintype.card A : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact (div_lt_iff₀ (by positivity :
      0 < Real.sqrt (Fintype.card A : ℝ))).2 (by simpa using hsqrt)
  have hdpos : 0 < 1 - r ^ 2 := by nlinarith
  have hbpos : 0 < 1 + r := by linarith
  have hnorm :
      ‖(((activityBasisMatrix (A := A) (n := n))ᵀ *
        activityBasisMatrix (A := A) (n := n))⁻¹)‖ ≤
        ((1 - r ^ 2) ^ n)⁻¹ * (1 + r) ^ n := by
    rw [activityBasisMatrix_gram_inverse u hu, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr (pow_pos hdpos _))]
    exact mul_le_mul_of_nonneg_left
      (booleanActivityGramKernel_negative_twoNorm_le r hrpos.le)
      (inv_nonneg.mpr (pow_nonneg hdpos.le _))
  have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  have hcancel : ((1 - r ^ 2) ^ n)⁻¹ * (1 + r) ^ n =
      ((1 - r) ^ n)⁻¹ := by
    rw [hfactor, mul_pow, mul_inv_rev]
    calc
      ((1 + r) ^ n)⁻¹ * ((1 - r) ^ n)⁻¹ * (1 + r) ^ n =
          ((1 - r) ^ n)⁻¹ * (((1 + r) ^ n)⁻¹ * (1 + r) ^ n) := by ring
      _ = ((1 - r) ^ n)⁻¹ := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hbpos)), mul_one]
  change ‖(((activityBasisMatrix (A := A) (n := n))ᵀ *
    activityBasisMatrix (A := A) (n := n))⁻¹)‖ ≤ ((1 - r) ^ n)⁻¹
  exact hnorm.trans_eq hcancel

/-- The paper's centered activity-matrix entry, expressed solely in terms of
the alphabet size and the two activity patterns. -/
noncomputable def activityCenteredCoordinate
    (q : ℕ) (x y : Fin n → Bool) : ℝ :=
  ((if n + 1 ≤ activityWeight x + activityWeight y then
      (q : ℝ) ^ (activityWeight x + activityWeight y - n)
    else 1) -
      (1 +
        (((q : ℝ) ^ activityWeight x - 1) *
          ((q : ℝ) ^ activityWeight y - 1)) /
            ((q : ℝ) ^ n - 1))) /
    Real.sqrt ((q : ℝ) ^ (activityWeight x + activityWeight y))

/-- A scalar inequality used for both activity-weight cases in the
Frobenius estimate. -/
private theorem centeredRatio_sq_le
    (Q d t : ℝ) (hQ : 1 < Q) (hd : 0 < d)
    (ht : t ^ 2 ≤ Q * d ^ 2) :
    (t / ((Q - 1) * d)) ^ 2 ≤ Q / (Q - 1) ^ 2 := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hden : 0 < (Q - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hQ)
  have htd : t ^ 2 / d ^ 2 ≤ Q := by
    apply (div_le_iff₀ hd2).2
    nlinarith [ht]
  calc
    (t / ((Q - 1) * d)) ^ 2 =
        (t ^ 2 / d ^ 2) / (Q - 1) ^ 2 := by
          field_simp [ne_of_gt hd, ne_of_gt (sub_pos.mpr hQ)]
          ring_nf
          simp
    _ ≤ Q / (Q - 1) ^ 2 := by
      exact (div_le_div_iff_of_pos_right hden).2 htd

/-- The low-activity numerator satisfies the squared estimate needed for
the uniform Frobenius entry bound. -/
private theorem centeredLow_product_sq_le
    (Q a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a * b ≤ Q) :
    ((a - 1) * (b - 1)) ^ 2 ≤ Q * (a * b) := by
  have hp : 0 ≤ a * b := mul_nonneg (by linarith) (by linarith)
  have ht : 0 ≤ (a - 1) * (b - 1) :=
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have htle : (a - 1) * (b - 1) ≤ a * b := by nlinarith [ha, hb]
  have hsq : ((a - 1) * (b - 1)) ^ 2 ≤ (a * b) ^ 2 :=
    (sq_le_sq₀ ht hp).2 htle
  have hsq2 : (a * b) ^ 2 ≤ Q * (a * b) := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hab)]
  exact hsq.trans hsq2

/-- The high-activity numerator has the same squared bound after the MDS
intersection term is rewritten as a product. -/
private theorem centeredHigh_product_sq_le
    (Q a b : ℝ) (hQ : 1 < Q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (haQ : a ≤ Q) (hbQ : b ≤ Q) (hab : Q ≤ a * b) :
    (((Q - a) * (Q - b)) / Q) ^ 2 ≤ Q * (a * b) := by
  have hQpos : 0 < Q := by linarith
  have hprod : (Q - a) * (Q - b) ≤ Q * Q := by
    gcongr <;> linarith
  have ht : 0 ≤ ((Q - a) * (Q - b)) / Q :=
    div_nonneg
      (mul_nonneg (sub_nonneg.mpr haQ) (sub_nonneg.mpr hbQ)) hQpos.le
  have htQ : ((Q - a) * (Q - b)) / Q ≤ Q := by
    apply (div_le_iff₀ hQpos).2
    nlinarith [hprod]
  have hsq : (((Q - a) * (Q - b)) / Q) ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ ht hQpos.le).2 htQ
  have hsq2 : Q ^ 2 ≤ Q * (a * b) := by
    nlinarith [mul_nonneg hQpos.le (sub_nonneg.mpr hab)]
  exact hsq.trans hsq2

/-- An activity pattern cannot have more active coordinates than its length. -/
theorem activityWeight_le_length (z : Fin n → Bool) : activityWeight z ≤ n := by
  unfold activityWeight
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun i : Fin n => z i = true) Finset.univ)

/-- The all-zero activity pattern. -/
def zeroActivityPattern : Fin n → Bool := fun _ => false

/-- The centered coordinate vanishes when its input pattern is all-zero. -/
theorem activityCenteredCoordinate_zero_left
    (q : ℕ) (y : Fin n → Bool) :
    activityCenteredCoordinate q (zeroActivityPattern (n := n)) y = 0 := by
  have hw : activityWeight (zeroActivityPattern (n := n)) = 0 := by
    simp [activityWeight, zeroActivityPattern]
  have hy := activityWeight_le_length y
  simp [activityCenteredCoordinate, hw, show ¬n + 1 ≤ activityWeight y by omega]

/-- The centered coordinate also vanishes when its output pattern is
all-zero. -/
theorem activityCenteredCoordinate_zero_right
    (q : ℕ) (x : Fin n → Bool) :
    activityCenteredCoordinate q x (zeroActivityPattern (n := n)) = 0 := by
  have hw : activityWeight (zeroActivityPattern (n := n)) = 0 := by
    simp [activityWeight, zeroActivityPattern]
  have hx := activityWeight_le_length x
  simp [activityCenteredCoordinate, hw, show ¬n + 1 ≤ activityWeight x by omega]

/-- Every centered activity entry obeys the same coarse squared bound. The
all-zero rows and columns, proved above, make this bound strong enough for the
closed-form Frobenius estimate. -/
theorem activityCenteredCoordinate_sq_le
    (q : ℕ) (hq : 2 ≤ q) (hn : 0 < n)
    (x y : Fin n → Bool) :
    (activityCenteredCoordinate q x y) ^ 2 ≤
      (q : ℝ) ^ n / ((q : ℝ) ^ n - 1) ^ 2 := by
  let qr : ℝ := q
  let a : ℝ := qr ^ activityWeight x
  let b : ℝ := qr ^ activityWeight y
  let Q : ℝ := qr ^ n
  let d : ℝ := Real.sqrt (qr ^ (activityWeight x + activityWeight y))
  have hqr : 1 < qr := by
    dsimp [qr]
    exact_mod_cast (show 1 < q by omega)
  have hqr1 : 1 ≤ qr := le_of_lt hqr
  have hQ : 1 < Q := one_lt_pow₀ hqr (Nat.ne_of_gt hn)
  have ha : 1 ≤ a := one_le_pow₀ hqr1
  have hb : 1 ≤ b := one_le_pow₀ hqr1
  have haQ : a ≤ Q := pow_le_pow_right₀ hqr1 (activityWeight_le_length x)
  have hbQ : b ≤ Q := pow_le_pow_right₀ hqr1 (activityWeight_le_length y)
  have hd : 0 < d := by
    dsimp [d]
    exact Real.sqrt_pos.2 (pow_pos (by linarith : 0 < qr) _)
  have hd2 : d ^ 2 = a * b := by
    dsimp [d, a, b]
    rw [Real.sq_sqrt (pow_nonneg (by linarith : 0 ≤ qr) _), pow_add]
  by_cases hhigh : n + 1 ≤ activityWeight x + activityWeight y
  · have hab : Q ≤ a * b := by
      have hp : a * b = qr ^ (activityWeight x + activityWeight y) := by
        dsimp [a, b]
        rw [pow_add]
      rw [hp]
      change qr ^ n ≤ qr ^ (activityWeight x + activityWeight y)
      exact pow_le_pow_right₀ hqr1 (by omega)
    let t : ℝ := -((Q - a) * (Q - b) / Q)
    have ht : t ^ 2 ≤ Q * d ^ 2 := by
      dsimp [t]
      rw [neg_sq, hd2]
      exact centeredHigh_product_sq_le Q a b hQ ha hb haQ hbQ hab
    have hpow : qr ^ (activityWeight x + activityWeight y - n) * Q = a * b := by
      dsimp [Q, a, b]
      rw [← pow_add, Nat.sub_add_cancel (by omega), pow_add]
    have hnum :
        qr ^ (activityWeight x + activityWeight y - n) -
          (1 + (a - 1) * (b - 1) / (Q - 1)) =
            -((Q - a) * (Q - b)) / (Q * (Q - 1)) := by
      field_simp [ne_of_gt (by linarith : (0 : ℝ) < Q),
        ne_of_gt (sub_pos.mpr hQ)]
      linear_combination (Q - 1) ^ 2 * hpow
    have hcoordinate : activityCenteredCoordinate q x y = t / ((Q - 1) * d) := by
      unfold activityCenteredCoordinate
      rw [if_pos hhigh]
      change (qr ^ (activityWeight x + activityWeight y - n) -
        (1 + (a - 1) * (b - 1) / (Q - 1))) / d =
          t / ((Q - 1) * d)
      rw [hnum]
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hQ), ne_of_gt hd,
        ne_of_gt (by linarith : (0 : ℝ) < Q)]
      simp [mul_assoc]
    rw [hcoordinate]
    exact centeredRatio_sq_le Q d t hQ hd ht
  · have hlow : activityWeight x + activityWeight y ≤ n := by omega
    have hab : a * b ≤ Q := by
      change qr ^ activityWeight x * qr ^ activityWeight y ≤ qr ^ n
      rw [← pow_add]
      exact pow_le_pow_right₀ hqr1 hlow
    let t : ℝ := -((a - 1) * (b - 1))
    have ht : t ^ 2 ≤ Q * d ^ 2 := by
      dsimp [t]
      rw [neg_sq, hd2]
      exact centeredLow_product_sq_le Q a b ha hb hab
    have hcoordinate : activityCenteredCoordinate q x y = t / ((Q - 1) * d) := by
      dsimp [activityCenteredCoordinate, t]
      rw [if_neg hhigh]
      dsimp [Q, a, b, d, qr]
      field_simp [ne_of_gt (sub_pos.mpr hQ), ne_of_gt hd]
    rw [hcoordinate]
    exact centeredRatio_sq_le Q d t hQ hd ht

/-- The Frobenius square is bounded by the number of pairs of nonzero
activity patterns times the uniform entry bound.

**Deviation from the paper:** the paper splits activity pairs by total
weight and uses a `7/8` counting factor. Here the zero-pattern row and
column are removed, leaving `(2^n-1)^2` pairs; this gives the same target
bound with a shorter combinatorial argument. -/
theorem activityCenteredFrobeniusSum_le_nonzeroCount
    (q : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
      (activityCenteredCoordinate q x y) ^ 2) ≤
      (((2 : ℝ) ^ n - 1) ^ 2) *
        ((q : ℝ) ^ n / ((q : ℝ) ^ n - 1) ^ 2) := by
  let z : Fin n → Bool := zeroActivityPattern (n := n)
  let S : Finset (Fin n → Bool) := Finset.univ.erase z
  let C : ℝ := (q : ℝ) ^ n / ((q : ℝ) ^ n - 1) ^ 2
  have hsumx (y : Fin n → Bool) :
      (∑ x : Fin n → Bool, (activityCenteredCoordinate q x y) ^ 2) =
        ∑ x ∈ S, (activityCenteredCoordinate q x y) ^ 2 := by
    have hzero : (activityCenteredCoordinate q z y) ^ 2 = 0 := by
      simp [z, activityCenteredCoordinate_zero_left]
    simpa [S] using (Finset.sum_erase Finset.univ
      (a := z) (f := fun x => (activityCenteredCoordinate q x y) ^ 2) hzero).symm
  have hsumy :
      (∑ y : Fin n → Bool, ∑ x ∈ S,
        (activityCenteredCoordinate q x y) ^ 2) =
        ∑ y ∈ S, ∑ x ∈ S,
          (activityCenteredCoordinate q x y) ^ 2 := by
    have hzero : (∑ x ∈ S, (activityCenteredCoordinate q x z) ^ 2) = 0 := by
      simp [z, activityCenteredCoordinate_zero_right]
    simpa [S] using (Finset.sum_erase Finset.univ
      (a := z) (f := fun y => ∑ x ∈ S,
        (activityCenteredCoordinate q x y) ^ 2) hzero).symm
  have hcard : (S.card : ℝ) = (2 : ℝ) ^ n - 1 := by
    have hnat : S.card = 2 ^ n - 1 := by simp [S]
    have hone : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    rw [hnat, Nat.cast_sub hone]
    norm_num
  calc
    (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
      (activityCenteredCoordinate q x y) ^ 2) =
        ∑ y ∈ S, ∑ x ∈ S,
          (activityCenteredCoordinate q x y) ^ 2 := by
      simp_rw [hsumx]
      exact hsumy
    _ ≤ ∑ y ∈ S, ∑ _x ∈ S, C := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro x _
      exact activityCenteredCoordinate_sq_le q hq hn x y
    _ = (((2 : ℝ) ^ n - 1) ^ 2) * C := by
      simp [hcard]
      ring

/-- Elementary inequality behind the zero-row/column counting argument. -/
private theorem nonzeroPatternCount_ratio_le
    (m Q : ℝ) (hm : 1 < m) (hQm : m ≤ Q) :
    (m - 1) ^ 2 * (Q / (Q - 1) ^ 2) ≤ m ^ 2 / Q := by
  have hQ : 1 < Q := hm.trans_le hQm
  have hden : 0 < (Q - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hQ)
  have hQpos : 0 < Q := by linarith
  have hcomp : (m - 1) * Q ≤ m * (Q - 1) := by nlinarith [hQm]
  have hsq : ((m - 1) * Q) ^ 2 ≤ (m * (Q - 1)) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by linarith) hQpos.le)
      (mul_nonneg (by linarith) (sub_pos.mpr hQ).le)).2 hcomp
  calc
    (m - 1) ^ 2 * (Q / (Q - 1) ^ 2) =
        ((m - 1) ^ 2 * Q) / (Q - 1) ^ 2 := by ring
    _ ≤ m ^ 2 / Q := by
      apply (div_le_div_iff₀ hden hQpos).2
      nlinarith [hsq]

/-- The centered activity matrix's exact Frobenius square satisfies the
simple closed-form bound needed for Theorem 3. This proof uses the alternative
zero-row/column count documented above. -/
theorem activityCenteredFrobeniusSum_le_closedForm
    (q : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
      (activityCenteredCoordinate q x y) ^ 2) ≤
        (2 : ℝ) ^ (2 * n) / (q : ℝ) ^ n := by
  let m : ℝ := (2 : ℝ) ^ n
  let Q : ℝ := (q : ℝ) ^ n
  have hm : 1 < m := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
    (Nat.ne_of_gt hn)
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hQm : m ≤ Q := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hqreal n
  have hbound := activityCenteredFrobeniusSum_le_nonzeroCount q hq hn
  have hratio := nonzeroPatternCount_ratio_le m Q hm hQm
  have hm2 : m ^ 2 = (2 : ℝ) ^ (2 * n) := by
    dsimp [m]
    rw [← pow_mul]
    ring
  calc
    (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
      (activityCenteredCoordinate q x y) ^ 2) ≤ m ^ 2 / Q :=
      hbound.trans hratio
    _ = (2 : ℝ) ^ (2 * n) / (q : ℝ) ^ n := by rw [hm2]

/-- For every MDS linear layer, its centered activity matrix has the same
explicit entries. The S-box does not appear in this expression. -/
theorem linear_centered_activityBasisMatrix_coordinate_eq
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (x y : Fin n → Bool) :
    ((activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
        activityBasisMatrix (A := A) (n := n)) y x =
      activityCenteredCoordinate (Fintype.card A) x y := by
  unfold activityCenteredCoordinate
  have hcard : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : A)⟩)
  have hsqrt : Real.sqrt ((Fintype.card A : ℝ) ^
      (activityWeight x + activityWeight y)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (pow_pos hcard _))
  apply (eq_div_iff hsqrt).2
  simpa only [mul_comm] using
    (linear_centered_activityBasisMatrix_coordinate L hMDS x y)

open scoped Matrix.Norms.L2Operator in
/-- The matrix two-norm of the MDS truncated coordinates is controlled by
the exact finite Frobenius sum of the paper's closed-form entries. -/
theorem linear_centered_activityBasisMatrix_twoNorm_le_exactFrobenius
    (L : State A n ≃+ State A n) (hMDS : IsMDS L) :
    ‖(activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
        activityBasisMatrix (A := A) (n := n)‖ ≤
      Real.sqrt (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
        (activityCenteredCoordinate (Fintype.card A) x y) ^ 2) := by
  convert matrixTwoNorm_le_sqrt_sum_entries_sq
    ((activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
        activityBasisMatrix (A := A) (n := n)) using 1
  simp_rw [linear_centered_activityBasisMatrix_coordinate_eq L hMDS]

open scoped Matrix.Norms.L2Operator in
/-- The closed-form two-norm estimate for the centered activity matrix
`Bᵀ(Dᴸ-U)B`. The Gram conversion below carries this estimate to the actual
projected operator. -/
theorem linear_centered_activityBasisMatrix_twoNorm_le_closedForm
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hq : 2 ≤ Fintype.card A) (hn : 0 < n) :
    ‖(activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
        activityBasisMatrix (A := A) (n := n)‖ ≤
      (2 / Real.sqrt (Fintype.card A : ℝ)) ^ n := by
  let q : ℝ := Fintype.card A
  have hqpos : 0 ≤ q := by dsimp [q]; positivity
  have hnum : Real.sqrt ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ n := by
    rw [show 2 * n = n * 2 by omega, pow_mul,
      Real.sqrt_sq (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  have hsqrtpow (m : ℕ) : Real.sqrt (q ^ m) = (Real.sqrt q) ^ m := by
    induction m with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hqpos k), ih, pow_succ]
  have hden : Real.sqrt (q ^ n) = (Real.sqrt q) ^ n := hsqrtpow n
  have hroot : Real.sqrt ((2 : ℝ) ^ (2 * n) / q ^ n) =
      (2 / Real.sqrt q) ^ n := by
    rw [Real.sqrt_div (by positivity), hnum, hden, div_pow]
  calc
    ‖(activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
        activityBasisMatrix (A := A) (n := n)‖ ≤
      Real.sqrt (∑ y : Fin n → Bool, ∑ x : Fin n → Bool,
        (activityCenteredCoordinate (Fintype.card A) x y) ^ 2) :=
      linear_centered_activityBasisMatrix_twoNorm_le_exactFrobenius L hMDS
    _ ≤ Real.sqrt ((2 : ℝ) ^ (2 * n) / q ^ n) :=
      Real.sqrt_le_sqrt (activityCenteredFrobeniusSum_le_closedForm
        (Fintype.card A) hq hn)
    _ = (2 / Real.sqrt (Fintype.card A : ℝ)) ^ n := hroot

open scoped Matrix.Norms.L2Operator in
/-- The paper's closed-form truncated-differential bound in the
orthonormalized activity basis `C = B R`. -/
theorem linear_centered_orthonormalActivityMatrix_twoNorm_le_closedForm
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hq : 2 ≤ Fintype.card A) (hn : 0 < n) :
    ‖(activityOrthonormalBasisMatrix (n := n) u hu)ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
      activityOrthonormalBasisMatrix (n := n) u hu‖ ≤
        (2 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ n := by
  let s := Real.sqrt (Fintype.card A : ℝ)
  let r := 1 / s
  let B := activityBasisMatrix (A := A) (n := n)
  let C := activityOrthonormalBasisMatrix (n := n) u hu
  let M := deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a) -
    uniformDifferenceDistributionMatrix (State A n)
  have hqreal : (1 : ℝ) < Fintype.card A := by
    exact_mod_cast (show 1 < Fintype.card A by omega)
  have hs : 1 < s := by
    dsimp [s]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hqreal
  have hspos : 0 < s := by linarith
  have hrlt : r < 1 := by
    dsimp [r]
    exact (div_lt_iff₀ hspos).2 (by simpa using hs)
  have hnonneg : 0 ≤ ((1 - r) ^ n)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by linarith : 0 ≤ 1 - r) _)
  have hbase : (1 - r)⁻¹ * (2 / s) = 2 / (s - 1) := by
    dsimp [r]
    field_simp [ne_of_gt hspos, ne_of_gt (sub_pos.mpr hs)]
    ring
  have hpow : ((1 - r) ^ n)⁻¹ * (2 / s) ^ n =
      (2 / (s - 1)) ^ n := by
    rw [← inv_pow, ← mul_pow, hbase]
  calc
    ‖Cᵀ * M * C‖ ≤ ‖(Bᵀ * B)⁻¹‖ * ‖Bᵀ * M * B‖ :=
      activityOrthonormalBasisMatrix_compression_twoNorm_le u hu M
    _ ≤ ((1 - r) ^ n)⁻¹ * ‖Bᵀ * M * B‖ :=
      mul_le_mul_of_nonneg_right
        (activityBasisMatrix_gram_inverse_twoNorm_le u hu) (norm_nonneg _)
    _ ≤ ((1 - r) ^ n)⁻¹ * (2 / s) ^ n :=
      mul_le_mul_of_nonneg_left
        (linear_centered_activityBasisMatrix_twoNorm_le_closedForm L hMDS hq hn)
        hnonneg
    _ = (2 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ n := hpow

open scoped Matrix.Norms.L2Operator in
/-- The paper's closed-form estimate for the actual truncated-differential
operator of an MDS linear layer. -/
theorem linear_centered_truncatedNorm_le_closedForm
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hq : 2 ≤ Fintype.card A) (hn : 0 < n) :
    ‖activityTruncatedOperator
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n))‖ ≤
      (2 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ n := by
  exact (activityTruncatedOperator_norm_le_compression u hu _).trans
    (linear_centered_orthonormalActivityMatrix_twoNorm_le_closedForm
      u hu L hMDS hq hn)

open scoped Matrix.Norms.L2Operator in
/-- The paper's truncated-differential theorem, stated without the auxiliary
choice of a nonzero alphabet element used to construct the activity basis.
The paper assumes `q ≥ 4` and `n ≥ 2`. -/
theorem sharkTruncatedDifferential
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hq : 4 ≤ Fintype.card A) (hn : 2 ≤ n) :
    ‖activityTruncatedOperator
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n))‖ ≤
      (2 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ n := by
  have hnonzero : ∃ u : A, u ≠ 0 := by
    by_contra h
    push_neg at h
    letI : Unique A := { default := 0, uniq := fun x => h x }
    have hcard : Fintype.card A = 1 := Fintype.card_unique
    omega
  obtain ⟨u, hu⟩ := hnonzero
  exact linear_centered_truncatedNorm_le_closedForm
    u hu L hMDS (by omega) (by omega)

end PairwiseIndependence

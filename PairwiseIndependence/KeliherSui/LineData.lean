import PairwiseIndependence.KeliherSui.ScalarCertificate

/-!
# The 56 affine lines of the MixColumns graph

Each record chooses three fixed graph coordinates, an ordering of the five
remaining coordinates, a nonzero kernel direction, and the inverse map for
the first four remaining coordinates. The small finite identities below
check this generated data against the concrete AES implementation.
-/

namespace PairwiseIndependence

abbrev KeliherSuiGraphIndex := Sum (Fin 4) (Fin 4)

def keliherSuiGraphIndex (i : Fin 8) : KeliherSuiGraphIndex :=
  if h : i.val < 4 then Sum.inl ⟨i.val, h⟩
  else Sum.inr ⟨i.val - 4, by omega⟩

structure KeliherSuiLineData where
  order : Array (Fin 8)
  direction : Array (Fin 256)
  coefficients : Array (Fin 256)
  inverse : Array (Array (Fin 256))
  deriving Inhabited

def keliherSuiLines : Array KeliherSuiLineData :=
#[
  ⟨#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 0, 0, 1], #[1, 1, 1, 3, 2], #[#[140, 53, 93, 1], #[141, 229, 52, 0], #[141, 92, 229, 0], #[141, 141, 141, 0]]⟩,
  ⟨#[0, 1, 3, 2, 4, 5, 6, 7], #[0, 0, 1, 0], #[1, 1, 3, 2, 1], #[#[154, 183, 1, 236], #[118, 155, 0, 91], #[45, 118, 0, 192], #[192, 91, 0, 118]]⟩,
  ⟨#[0, 2, 3, 1, 4, 5, 6, 7], #[0, 1, 0, 0], #[1, 3, 2, 1, 1], #[#[168, 1, 113, 57], #[145, 0, 217, 225], #[225, 0, 145, 72], #[217, 0, 56, 145]]⟩,
  ⟨#[1, 2, 3, 0, 4, 5, 6, 7], #[1, 0, 0, 0], #[1, 2, 1, 1, 3], #[#[1, 38, 159, 247], #[0, 246, 246, 246], #[0, 79, 39, 246], #[0, 158, 79, 246]]⟩,
  ⟨#[0, 1, 4, 2, 5, 3, 6, 7], #[0, 0, 1, 1], #[1, 2, 1, 1, 3], #[#[244, 246, 1, 0], #[246, 246, 0, 0], #[244, 247, 0, 1], #[247, 246, 0, 0]]⟩,
  ⟨#[0, 2, 4, 1, 5, 3, 6, 7], #[0, 1, 0, 3], #[1, 1, 3, 4, 7], #[#[7, 1, 3, 0], #[2, 0, 1, 0], #[7, 0, 2, 1], #[3, 0, 1, 0]]⟩,
  ⟨#[1, 2, 4, 0, 5, 3, 6, 7], #[1, 0, 0, 2], #[1, 3, 2, 7, 7], #[#[1, 209, 104, 0], #[0, 185, 209, 0], #[0, 1, 1, 1], #[0, 104, 185, 0]]⟩,
  ⟨#[0, 3, 4, 1, 5, 2, 6, 7], #[0, 1, 3, 0], #[1, 7, 3, 7, 2], #[#[142, 1, 0, 140], #[140, 0, 0, 141], #[142, 0, 1, 141], #[141, 0, 0, 141]]⟩,
  ⟨#[1, 3, 4, 0, 5, 2, 6, 7], #[1, 0, 2, 0], #[1, 7, 2, 5, 1], #[#[1, 185, 0, 104], #[0, 104, 0, 209], #[0, 1, 1, 1], #[0, 209, 0, 185]]⟩,
  ⟨#[2, 3, 4, 0, 5, 1, 6, 7], #[1, 247, 0, 0], #[1, 244, 247, 246, 244], #[#[1, 0, 185, 209], #[0, 0, 104, 185], #[0, 1, 1, 1], #[0, 0, 209, 104]]⟩,
  ⟨#[0, 1, 5, 2, 4, 3, 6, 7], #[0, 0, 1, 3], #[1, 2, 3, 7, 7], #[#[7, 5, 1, 0], #[1, 1, 0, 0], #[4, 7, 0, 1], #[3, 2, 0, 0]]⟩,
  ⟨#[0, 2, 5, 1, 4, 3, 6, 7], #[0, 1, 0, 2], #[1, 1, 2, 7, 5], #[#[165, 1, 82, 0], #[164, 0, 82, 0], #[82, 0, 165, 1], #[82, 0, 164, 0]]⟩,
  ⟨#[1, 2, 5, 0, 4, 3, 6, 7], #[1, 0, 0, 1], #[1, 3, 1, 2, 1], #[#[1, 184, 209, 0], #[0, 185, 209, 0], #[0, 209, 105, 1], #[0, 209, 104, 0]]⟩,
  ⟨#[0, 3, 5, 1, 4, 2, 6, 7], #[0, 1, 247, 0], #[1, 244, 247, 244, 246], #[#[105, 1, 0, 209], #[104, 0, 0, 209], #[209, 0, 1, 184], #[209, 0, 0, 185]]⟩,
  ⟨#[1, 3, 5, 0, 4, 2, 6, 7], #[1, 0, 246, 0], #[1, 244, 246, 246, 245], #[#[1, 71, 0, 203], #[0, 70, 0, 203], #[0, 203, 1, 71], #[0, 203, 0, 70]]⟩,
  ⟨#[2, 3, 5, 0, 4, 1, 6, 7], #[1, 141, 0, 0], #[1, 142, 141, 140, 142], #[#[1, 0, 7, 5], #[0, 0, 3, 2], #[0, 1, 4, 7], #[0, 0, 1, 1]]⟩,
  ⟨#[0, 4, 5, 1, 6, 3, 2, 7], #[0, 1, 141, 142], #[1, 137, 142, 141, 139], #[#[1, 1, 0, 0], #[1, 0, 0, 0], #[3, 0, 0, 1], #[2, 0, 1, 0]]⟩,
  ⟨#[1, 4, 5, 0, 6, 3, 2, 7], #[1, 0, 140, 142], #[1, 139, 142, 140, 136], #[#[1, 1, 0, 0], #[0, 1, 0, 0], #[0, 3, 0, 1], #[0, 2, 1, 0]]⟩,
  ⟨#[2, 4, 5, 0, 6, 3, 1, 7], #[1, 3, 0, 7], #[1, 11, 7, 3, 14], #[#[1, 0, 141, 0], #[0, 0, 141, 0], #[0, 0, 140, 1], #[0, 1, 141, 0]]⟩,
  ⟨#[3, 4, 5, 0, 6, 2, 1, 7], #[1, 1, 1, 0], #[1, 2, 1, 1, 3], #[#[1, 0, 0, 246], #[0, 0, 0, 246], #[0, 0, 1, 247], #[0, 1, 0, 246]]⟩,
  ⟨#[0, 1, 6, 2, 4, 3, 5, 7], #[0, 0, 1, 247], #[1, 246, 247, 244, 244], #[#[1, 1, 1, 0], #[185, 209, 0, 0], #[209, 104, 0, 1], #[104, 185, 0, 0]]⟩,
  ⟨#[0, 2, 6, 1, 4, 3, 5, 7], #[0, 1, 0, 246], #[1, 245, 246, 244, 246], #[#[1, 1, 1, 0], #[104, 0, 209, 0], #[185, 0, 104, 1], #[209, 0, 185, 0]]⟩,
  ⟨#[1, 2, 6, 0, 4, 3, 5, 7], #[1, 0, 0, 246], #[1, 244, 246, 247, 244], #[#[1, 1, 1, 0], #[0, 104, 185, 0], #[0, 185, 209, 1], #[0, 209, 104, 0]]⟩,
  ⟨#[0, 3, 6, 1, 4, 2, 5, 7], #[0, 1, 141, 0], #[1, 142, 141, 142, 140], #[#[246, 1, 0, 244], #[246, 0, 0, 246], #[247, 0, 1, 244], #[246, 0, 0, 247]]⟩,
  ⟨#[1, 3, 6, 0, 4, 2, 5, 7], #[1, 0, 141, 0], #[1, 143, 141, 141, 142], #[#[1, 3, 0, 7], #[0, 1, 0, 2], #[0, 2, 1, 7], #[0, 1, 0, 3]]⟩,
  ⟨#[2, 3, 6, 0, 4, 1, 5, 7], #[1, 1, 0, 0], #[1, 1, 1, 3, 2], #[#[1, 0, 140, 142], #[0, 0, 141, 140], #[0, 1, 141, 142], #[0, 0, 141, 141]]⟩,
  ⟨#[0, 4, 6, 1, 5, 3, 2, 7], #[0, 1, 4, 7], #[1, 9, 7, 4, 11], #[#[2, 1, 0, 0], #[1, 0, 0, 0], #[1, 0, 0, 1], #[3, 0, 1, 0]]⟩,
  ⟨#[1, 4, 6, 0, 5, 3, 2, 7], #[1, 0, 7, 5], #[1, 13, 5, 7, 14], #[#[1, 141, 0, 0], #[0, 141, 0, 0], #[0, 141, 0, 1], #[0, 140, 1, 0]]⟩,
  ⟨#[2, 4, 6, 0, 5, 3, 1, 7], #[1, 71, 0, 203], #[1, 68, 203, 71, 201], #[#[1, 0, 246, 0], #[0, 0, 246, 0], #[0, 0, 246, 1], #[0, 1, 247, 0]]⟩,
  ⟨#[3, 4, 6, 0, 5, 2, 1, 7], #[1, 184, 209, 0], #[1, 2, 209, 184, 106], #[#[1, 0, 0, 1], #[0, 0, 0, 1], #[0, 0, 1, 3], #[0, 1, 0, 2]]⟩,
  ⟨#[0, 5, 6, 1, 4, 3, 2, 7], #[0, 1, 1, 1], #[1, 3, 1, 1, 2], #[#[140, 1, 0, 0], #[141, 0, 0, 0], #[141, 0, 0, 1], #[141, 0, 1, 0]]⟩,
  ⟨#[1, 5, 6, 0, 4, 3, 2, 7], #[1, 0, 185, 209], #[1, 106, 209, 185, 3], #[#[1, 247, 0, 0], #[0, 246, 0, 0], #[0, 246, 0, 1], #[0, 246, 1, 0]]⟩,
  ⟨#[2, 5, 6, 0, 4, 3, 1, 7], #[1, 185, 0, 104], #[1, 186, 104, 185, 106], #[#[1, 0, 2, 0], #[0, 0, 1, 0], #[0, 0, 1, 1], #[0, 1, 3, 0]]⟩,
  ⟨#[3, 5, 6, 0, 4, 2, 1, 7], #[1, 209, 104, 0], #[1, 2, 104, 209, 186], #[#[1, 0, 0, 2], #[0, 0, 0, 1], #[0, 0, 1, 1], #[0, 1, 0, 3]]⟩,
  ⟨#[4, 5, 6, 0, 7, 2, 3, 1], #[1, 38, 159, 247], #[1, 79, 159, 247, 38], #[#[1, 3, 0, 0], #[0, 1, 0, 0], #[0, 1, 1, 0], #[0, 2, 0, 1]]⟩,
  ⟨#[0, 1, 7, 2, 4, 3, 5, 6], #[0, 0, 1, 141], #[1, 140, 141, 142, 142], #[#[1, 1, 1, 0], #[185, 209, 0, 0], #[209, 104, 0, 1], #[104, 185, 0, 0]]⟩,
  ⟨#[0, 2, 7, 1, 4, 3, 5, 6], #[0, 1, 0, 141], #[1, 142, 141, 143, 141], #[#[1, 1, 1, 0], #[104, 0, 209, 0], #[185, 0, 104, 1], #[209, 0, 185, 0]]⟩,
  ⟨#[1, 2, 7, 0, 4, 3, 5, 6], #[1, 0, 0, 140], #[1, 142, 140, 141, 142], #[#[1, 1, 1, 0], #[0, 104, 185, 0], #[0, 185, 209, 1], #[0, 209, 104, 0]]⟩,
  ⟨#[0, 3, 7, 1, 4, 2, 5, 6], #[0, 1, 1, 0], #[1, 2, 1, 1, 3], #[#[246, 1, 0, 244], #[246, 0, 0, 246], #[247, 0, 1, 244], #[246, 0, 0, 247]]⟩,
  ⟨#[1, 3, 7, 0, 4, 2, 5, 6], #[1, 0, 3, 0], #[1, 1, 3, 4, 7], #[#[1, 3, 0, 7], #[0, 1, 0, 2], #[0, 2, 1, 7], #[0, 1, 0, 3]]⟩,
  ⟨#[2, 3, 7, 0, 4, 1, 5, 6], #[1, 3, 0, 0], #[1, 7, 3, 7, 2], #[#[1, 0, 140, 142], #[0, 0, 141, 140], #[0, 1, 141, 142], #[0, 0, 141, 141]]⟩,
  ⟨#[0, 4, 7, 1, 5, 3, 2, 6], #[0, 1, 244, 247], #[1, 242, 247, 244, 240], #[#[2, 1, 0, 0], #[1, 0, 0, 0], #[1, 0, 0, 1], #[3, 0, 1, 0]]⟩,
  ⟨#[1, 4, 7, 0, 5, 3, 2, 6], #[1, 0, 244, 246], #[1, 240, 246, 244, 243], #[#[1, 141, 0, 0], #[0, 141, 0, 0], #[0, 141, 0, 1], #[0, 140, 1, 0]]⟩,
  ⟨#[2, 4, 7, 0, 5, 3, 1, 6], #[1, 1, 0, 1], #[1, 2, 1, 1, 3], #[#[1, 0, 246, 0], #[0, 0, 246, 0], #[0, 0, 246, 1], #[0, 1, 247, 0]]⟩,
  ⟨#[3, 4, 7, 0, 5, 2, 1, 6], #[1, 141, 142, 0], #[1, 137, 142, 141, 139], #[#[1, 0, 0, 1], #[0, 0, 0, 1], #[0, 0, 1, 3], #[0, 1, 0, 2]]⟩,
  ⟨#[0, 5, 7, 1, 4, 3, 2, 6], #[0, 1, 184, 209], #[1, 106, 209, 184, 2], #[#[140, 1, 0, 0], #[141, 0, 0, 0], #[141, 0, 0, 1], #[141, 0, 1, 0]]⟩,
  ⟨#[1, 5, 7, 0, 4, 3, 2, 6], #[1, 0, 209, 105], #[1, 186, 105, 209, 3], #[#[1, 247, 0, 0], #[0, 246, 0, 0], #[0, 246, 0, 1], #[0, 246, 1, 0]]⟩,
  ⟨#[2, 5, 7, 0, 4, 3, 1, 6], #[1, 82, 0, 165], #[1, 81, 165, 82, 167], #[#[1, 0, 2, 0], #[0, 0, 1, 0], #[0, 0, 1, 1], #[0, 1, 3, 0]]⟩,
  ⟨#[3, 5, 7, 0, 4, 2, 1, 6], #[1, 4, 7, 0], #[1, 9, 7, 4, 11], #[#[1, 0, 0, 2], #[0, 0, 0, 1], #[0, 0, 1, 1], #[0, 1, 0, 3]]⟩,
  ⟨#[4, 5, 7, 0, 6, 2, 3, 1], #[1, 113, 57, 168], #[1, 225, 57, 168, 113], #[#[1, 1, 0, 0], #[0, 1, 0, 0], #[0, 2, 1, 0], #[0, 3, 0, 1]]⟩,
  ⟨#[0, 6, 7, 1, 4, 3, 2, 5], #[0, 1, 209, 104], #[1, 186, 104, 209, 2], #[#[140, 1, 0, 0], #[141, 0, 0, 0], #[141, 0, 0, 1], #[141, 0, 1, 0]]⟩,
  ⟨#[1, 6, 7, 0, 4, 3, 2, 5], #[1, 0, 1, 1], #[1, 2, 1, 1, 3], #[#[1, 247, 0, 0], #[0, 246, 0, 0], #[0, 246, 0, 1], #[0, 246, 1, 0]]⟩,
  ⟨#[2, 6, 7, 0, 4, 3, 1, 5], #[1, 7, 0, 2], #[1, 9, 2, 7, 13], #[#[1, 0, 2, 0], #[0, 0, 1, 0], #[0, 0, 1, 1], #[0, 1, 3, 0]]⟩,
  ⟨#[3, 6, 7, 0, 4, 2, 1, 5], #[1, 244, 247, 0], #[1, 242, 247, 244, 240], #[#[1, 0, 0, 2], #[0, 0, 0, 1], #[0, 0, 1, 1], #[0, 1, 0, 3]]⟩,
  ⟨#[4, 6, 7, 0, 5, 2, 3, 1], #[1, 236, 154, 183], #[1, 192, 154, 183, 236], #[#[1, 141, 0, 0], #[0, 141, 0, 0], #[0, 140, 1, 0], #[0, 141, 0, 1]]⟩,
  ⟨#[5, 6, 7, 0, 4, 2, 3, 1], #[1, 140, 53, 93], #[1, 229, 53, 93, 140], #[#[1, 247, 0, 0], #[0, 246, 0, 0], #[0, 246, 1, 0], #[0, 246, 0, 1]]⟩
]

def keliherSuiLineFixed (s : Fin 56) : Finset KeliherSuiGraphIndex :=
  (Finset.univ : Finset (Fin 3)).image (fun i =>
    keliherSuiGraphIndex ((keliherSuiLines[s.val]!).order[i.val]!))

def keliherSuiLineFree (s : Fin 56) (i : Fin 5) : KeliherSuiGraphIndex :=
  keliherSuiGraphIndex ((keliherSuiLines[s.val]!).order[i.val + 3]!)

def keliherSuiLineCoefficient (s : Fin 56) (i : Fin 5) : Fin 256 :=
  (keliherSuiLines[s.val]!).coefficients[i.val]!

def keliherSuiLineDirection (s : Fin 56) (t : AesByte) : State AesByte 4 :=
  fun i => aesByteMul t
    (aesByteFinEquiv ((keliherSuiLines[s.val]!).direction[i.val]!))

def keliherSuiLineBasis (s : Fin 56) (j : Fin 4) (t : AesByte) : State AesByte 4 :=
  fun i => aesByteMul t
    (aesByteFinEquiv (((keliherSuiLines[s.val]!).inverse[j.val]!)[i.val]!))

def keliherSuiLineReconstruct (s : Fin 56) (v : Fin 4 → AesByte) : State AesByte 4 :=
  ∑ j : Fin 4, keliherSuiLineBasis s j (v j)

theorem keliherSuiLine_cover :
    ∀ R : Finset KeliherSuiGraphIndex, R.card = 3 →
      ∃ s : Fin 56, keliherSuiLineFixed s = R := by
  native_decide

theorem keliherSuiLine_indices : ∀ s : Fin 56,
    (keliherSuiLineFixed s).card = 3 ∧
    Function.Injective (keliherSuiLineFree s) ∧
    (Finset.univ.image (keliherSuiLineFree s)) =
      Finset.univ \ keliherSuiLineFixed s ∧
    (∃ i : Fin 4, keliherSuiLineFree s 0 = Sum.inl i) ∧
    (∃ i : Fin 4, keliherSuiLineFree s 1 = Sum.inr i) ∧
    (∀ i : Fin 5, keliherSuiLineCoefficient s i ≠ 0) ∧
    keliherSuiLineCoefficient s 0 = 1 := by
  native_decide

def keliherSuiGraphCoordinateHom (j : KeliherSuiGraphIndex) :
    State AesByte 4 →+ AesByte where
  toFun x := mdsGraphCoordinate aesMixColumnEquiv x j
  map_zero' := by cases j <;> simp [mdsGraphCoordinate]
  map_add' x y := by cases j <;> simp [mdsGraphCoordinate]

def keliherSuiDirectionTable (M : Array (Array (Fin 256))) :
    Array (Array (State AesByte 4)) :=
  Array.ofFn (fun s : Fin 56 => Array.ofFn (fun t : Fin 256 => fun i : Fin 4 =>
    aesByteFinEquiv ((M[((keliherSuiLines[s.val]!).direction[i.val]!).val]!)[t.val]!)))

theorem keliherSuiDirectionTable_get (s : Fin 56) (t : Fin 256) :
    ((keliherSuiDirectionTable keliherSuiMultiplication)[s.val]!)[t.val]! =
      keliherSuiLineDirection s (aesByteFinEquiv t) := by
  simp only [keliherSuiDirectionTable, keliherSui_ofFn_get]
  funext i
  exact keliherSuiMultiply_byte _ t

def KeliherSuiLineDirectionCheck (directions : Array (Array (State AesByte 4)))
    (M : Array (Array (Fin 256))) : Prop :=
  ∀ s : Fin 56, ∀ t : Fin 256,
    (∀ j ∈ keliherSuiLineFixed s,
      mdsGraphCoordinate aesMixColumnEquiv ((directions[s.val]!)[t.val]!) j = 0) ∧
    (∀ i : Fin 5,
      mdsGraphCoordinate aesMixColumnEquiv ((directions[s.val]!)[t.val]!)
        (keliherSuiLineFree s i) =
      aesByteFinEquiv ((M[(keliherSuiLineCoefficient s i).val]!)[t.val]!))

instance (directions : Array (Array (State AesByte 4)))
    (M : Array (Array (Fin 256))) : Decidable (KeliherSuiLineDirectionCheck directions M) :=
  inferInstanceAs (Decidable (∀ s : Fin 56, ∀ t : Fin 256,
    (∀ j ∈ keliherSuiLineFixed s,
      mdsGraphCoordinate aesMixColumnEquiv ((directions[s.val]!)[t.val]!) j = 0) ∧
    (∀ i : Fin 5,
      mdsGraphCoordinate aesMixColumnEquiv ((directions[s.val]!)[t.val]!)
        (keliherSuiLineFree s i) =
      aesByteFinEquiv ((M[(keliherSuiLineCoefficient s i).val]!)[t.val]!))))

/-- The generated direction lies in the kernel of the fixed coordinates. -/
theorem keliherSuiLineDirection_certificate :
    KeliherSuiLineDirectionCheck (keliherSuiDirectionTable keliherSuiMultiplication)
      keliherSuiMultiplication := by native_decide

def keliherSuiBasisTable (M : Array (Array (Fin 256))) :
    Array (Array (Array (State AesByte 4))) :=
  Array.ofFn (fun s : Fin 56 => Array.ofFn (fun j : Fin 4 =>
    Array.ofFn (fun t : Fin 256 => fun i : Fin 4 =>
      aesByteFinEquiv ((M[(((keliherSuiLines[s.val]!).inverse[j.val]!)[i.val]!).val]!)[t.val]!))))

theorem keliherSuiBasisTable_get (s : Fin 56) (j : Fin 4) (t : Fin 256) :
    (((keliherSuiBasisTable keliherSuiMultiplication)[s.val]!)[j.val]!)[t.val]! =
      keliherSuiLineBasis s j (aesByteFinEquiv t) := by
  simp only [keliherSuiBasisTable, keliherSui_ofFn_get]
  funext i
  exact keliherSuiMultiply_byte _ t

def KeliherSuiLineBasisCheck (basis : Array (Array (Array (State AesByte 4)))) : Prop :=
  ∀ (s : Fin 56) (j k : Fin 4) (t : Fin 256),
    mdsGraphCoordinate aesMixColumnEquiv (((basis[s.val]!)[j.val]!)[t.val]!)
      (keliherSuiLineFree s k.castSucc) =
      if k = j then aesByteFinEquiv t else 0

instance (basis : Array (Array (Array (State AesByte 4)))) :
    Decidable (KeliherSuiLineBasisCheck basis) :=
  inferInstanceAs (Decidable (∀ (s : Fin 56) (j k : Fin 4) (t : Fin 256),
    mdsGraphCoordinate aesMixColumnEquiv (((basis[s.val]!)[j.val]!)[t.val]!)
      (keliherSuiLineFree s k.castSucc) =
      if k = j then aesByteFinEquiv t else 0))

/-- The reconstruction columns invert the first four free coordinates. -/
theorem keliherSuiLineBasis_certificate :
    KeliherSuiLineBasisCheck (keliherSuiBasisTable keliherSuiMultiplication) := by
  native_decide

end PairwiseIndependence

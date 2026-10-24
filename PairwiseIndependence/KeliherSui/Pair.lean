import PairwiseIndependence.KeliherSui.Lookahead

/-!
# The first two factors in the Keliher--Sui search

The search uses the support of a difference-distribution row or column and
its unique count-four entry. These lemmas prove that this compact data
determines the exact product of two factors. The bitset intersection in the
standalone search is therefore an implementation of a mathematical identity,
not an additional cryptanalytic assumption.
-/

namespace PairwiseIndependence

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Indicator of a nonzero difference count. -/
def keliherSuiCountSupport (p : T → Nat) (t : T) : Nat :=
  if p t = 0 then 0 else 1

/-- Indicator of the distinguished count-four position. -/
def keliherSuiSpecialIndicator (s t : T) : Nat :=
  if t = s then 1 else 0

omit [Fintype T] in
/-- A nontrivial AES byte row or column has count zero or two at all
positions other than its unique count-four position. -/
theorem keliherSui_count_eq_support_plus_special
    (p : T → Nat) (s t : T)
    (hvalues : ∀ t, p t = 0 ∨ p t = 2 ∨ p t = 4)
    (hfour : ∀ t, p t = 4 ↔ t = s) :
    p t = 2 * keliherSuiCountSupport p t +
      2 * keliherSuiSpecialIndicator s t := by
  rcases hvalues t with hzero | htwo | hfour'
  · have hne : t ≠ s := by
      intro h
      have hh := (hfour t).2 h
      omega
    simp [keliherSuiCountSupport, keliherSuiSpecialIndicator, hzero, hne]
  · have hne : t ≠ s := by
      intro h
      have hh := (hfour t).2 h
      omega
    simp [keliherSuiCountSupport, keliherSuiSpecialIndicator, htwo, hne]
  · have heq : t = s := (hfour t).1 hfour'
    subst t
    simp [keliherSuiCountSupport, keliherSuiSpecialIndicator, hfour']

omit [Fintype T] in
/-- Exact two-factor identity underlying the support-intersection check.
Each ordinary intersection contributes four; either distinguished position
contributes a further four, including both when they coincide. -/
theorem keliherSui_pair_product_eq_support_formula
    (p q : T → Nat) (sp sq t : T)
    (hp : ∀ t, p t = 0 ∨ p t = 2 ∨ p t = 4)
    (hq : ∀ t, q t = 0 ∨ q t = 2 ∨ q t = 4)
    (hpfour : ∀ t, p t = 4 ↔ t = sp)
    (hqfour : ∀ t, q t = 4 ↔ t = sq) :
    p t * q t = 4 *
      (keliherSuiCountSupport p t * keliherSuiCountSupport q t +
        keliherSuiSpecialIndicator sp t * keliherSuiCountSupport q t +
        keliherSuiCountSupport p t * keliherSuiSpecialIndicator sq t +
        keliherSuiSpecialIndicator sp t *
          keliherSuiSpecialIndicator sq t) := by
  rw [keliherSui_count_eq_support_plus_special p sp t hp hpfour,
    keliherSui_count_eq_support_plus_special q sq t hq hqfour]
  ring

/-- Exact sum of the first two factors, in the form used by the finite
search. The first term is a support-intersection cardinality. -/
theorem keliherSui_pair_sum_eq_support_formula
    (p q : T → Nat) (sp sq : T)
    (hp : ∀ t, p t = 0 ∨ p t = 2 ∨ p t = 4)
    (hq : ∀ t, q t = 0 ∨ q t = 2 ∨ q t = 4)
    (hpfour : ∀ t, p t = 4 ↔ t = sp)
    (hqfour : ∀ t, q t = 4 ↔ t = sq) :
    (∑ t : T, p t * q t) = 4 *
      ((∑ t : T,
          keliherSuiCountSupport p t * keliherSuiCountSupport q t) +
        keliherSuiCountSupport q sp +
        keliherSuiCountSupport p sq +
        (if sp = sq then 1 else 0)) := by
  simp_rw [keliherSui_pair_product_eq_support_formula
    p q sp sq _ hp hq hpfour hqfour]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have hfirst :
      (∑ t : T, keliherSuiSpecialIndicator sp t *
        keliherSuiCountSupport q t) = keliherSuiCountSupport q sp := by
    simp [keliherSuiSpecialIndicator]
  have hsecond :
      (∑ t : T, keliherSuiCountSupport p t *
        keliherSuiSpecialIndicator sq t) = keliherSuiCountSupport p sq := by
    simp [keliherSuiSpecialIndicator]
  have hthird :
      (∑ t : T, keliherSuiSpecialIndicator sp t *
        keliherSuiSpecialIndicator sq t) =
          if sp = sq then 1 else 0 := by
    simp [keliherSuiSpecialIndicator, eq_comm]
  rw [hfirst, hsecond, hthird]

/-- The AES inverse-byte difference-count table has the exact three-valued
profile needed for the pair identity. This is checked on the stored table. -/
theorem aesInverseDifferenceCountTable_three_values :
    ∀ a b : Fin 256, a ≠ 0 ∨ b ≠ 0 →
      (aesInverseDifferenceCountTable[a.val]!)[b.val]! = 0 ∨
      (aesInverseDifferenceCountTable[a.val]!)[b.val]! = 2 ∨
      (aesInverseDifferenceCountTable[a.val]!)[b.val]! = 4 := by
  native_decide

/-- Every nonzero input AES S-box row is zero, two, or four. -/
theorem aesSboxDifferenceCountFin_row_three_values
    (a : Fin 256) (ha : a ≠ 0) (b : Fin 256) :
    aesSboxDifferenceCountFin a b = 0 ∨
    aesSboxDifferenceCountFin a b = 2 ∨
    aesSboxDifferenceCountFin a b = 4 := by
  rw [aesSboxDifferenceCountFin_index]
  exact aesInverseDifferenceCountTable_three_values
    a (aesInverseAffineDifferenceIndex b) (Or.inl ha)

/-- Every nonzero output AES S-box column is zero, two, or four. -/
theorem aesSboxDifferenceCountFin_column_three_values
    (b : Fin 256) (hb : b ≠ 0) (a : Fin 256) :
    aesSboxDifferenceCountFin a b = 0 ∨
    aesSboxDifferenceCountFin a b = 2 ∨
    aesSboxDifferenceCountFin a b = 4 := by
  have hzero : aesInverseAffineDifferenceIndex (0 : Fin 256) = 0 := by decide
  have hb' : aesInverseAffineDifferenceIndex b ≠ 0 := by
    intro hz
    exact hb (aesInverseAffineDifferenceIndex.injective
      (by simpa only [hzero] using hz))
  rw [aesSboxDifferenceCountFin_index]
  exact aesInverseDifferenceCountTable_three_values
    a (aesInverseAffineDifferenceIndex b) (Or.inr hb')

end PairwiseIndependence

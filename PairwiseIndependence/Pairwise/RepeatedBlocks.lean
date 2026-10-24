import PairwiseIndependence.Pairwise.Composition

/-!
# Repeating blocks with independent round keys

Each added block receives its own key and a fresh uniform intermediate state
key. The recursive key type is a product, so uniform averaging is uniform and
independent in every component. No key schedule is used.
-/

namespace PairwiseIndependence

universe u

/-- Keys for `r + 1` independently keyed blocks. -/
def RepeatedBlockKeys (κ A : Type u) : ℕ → Type u
  | 0 => κ
  | r + 1 => RepeatedBlockKeys κ A r × κ × A

private def repeatedBlockKeysFintype {κ A : Type u} [Fintype κ] [Fintype A] :
    (r : ℕ) → Fintype (RepeatedBlockKeys κ A r)
  | 0 => inferInstanceAs (Fintype κ)
  | r + 1 =>
      letI : Fintype (RepeatedBlockKeys κ A r) := repeatedBlockKeysFintype r
      inferInstanceAs (Fintype (RepeatedBlockKeys κ A r × κ × A))

instance {κ A : Type u} [Fintype κ] [Fintype A] (r : ℕ) :
    Fintype (RepeatedBlockKeys κ A r) := repeatedBlockKeysFintype r

private def repeatedBlockKeysNonempty {κ A : Type u} [Nonempty κ] [Nonempty A] :
    (r : ℕ) → Nonempty (RepeatedBlockKeys κ A r)
  | 0 => inferInstanceAs (Nonempty κ)
  | r + 1 =>
      letI : Nonempty (RepeatedBlockKeys κ A r) := repeatedBlockKeysNonempty r
      inferInstanceAs (Nonempty (RepeatedBlockKeys κ A r × κ × A))

instance {κ A : Type u} [Nonempty κ] [Nonempty A] (r : ℕ) :
    Nonempty (RepeatedBlockKeys κ A r) := repeatedBlockKeysNonempty r

variable {A κ : Type u} [AddCommGroup A] [Fintype A] [Fintype κ]

/-- `r + 1` copies of a keyed block, with independent block keys and a fresh
uniform additive key between consecutive blocks. -/
def repeatedBlocks (f : κ → A → A) :
    (r : ℕ) → RepeatedBlockKeys κ A r → A → A
  | 0, key, x => f key x
  | r + 1, key, x =>
      f key.2.1 (repeatedBlocks f r key.1 x + key.2.2)

omit [Fintype A] [Fintype κ] in
theorem repeatedBlocks_bijective
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) :
    ∀ (r : ℕ) (key : RepeatedBlockKeys κ A r),
      Function.Bijective (repeatedBlocks f r key)
  | 0, key => hf key
  | r + 1, key => by
      change Function.Bijective
        ((f key.2.1) ∘ (fun x : A => x + key.2.2) ∘
          repeatedBlocks f r key.1)
      exact (hf key.2.1).comp
        ((Equiv.addRight key.2.2).bijective.comp
          (repeatedBlocks_bijective f hf r key.1))

/-- The difference-distribution matrix of `r + 1` independent blocks is the
`r + 1`-st matrix power. This is the composition identity used in Corollary 2. -/
theorem repeatedBlocks_differenceDistributionMatrix [DecidableEq A]
    (f : κ → A → A) :
    ∀ r : ℕ,
      differenceDistributionMatrix (repeatedBlocks f r) =
        (differenceDistributionMatrix f) ^ (r + 1)
  | 0 => by simp [repeatedBlocks]
  | r + 1 => by
      calc
        differenceDistributionMatrix (repeatedBlocks f (r + 1)) =
            differenceDistributionMatrix
              (independentlyKeyedComposition (repeatedBlocks f r) f) := rfl
        _ = differenceDistributionMatrix f *
              differenceDistributionMatrix (repeatedBlocks f r) :=
          differenceDistributionMatrix_independentlyKeyedComposition _ _
        _ = differenceDistributionMatrix f *
              (differenceDistributionMatrix f) ^ (r + 1) := by
          rw [repeatedBlocks_differenceDistributionMatrix f r]
        _ = (differenceDistributionMatrix f) ^ (r + 1 + 1) := by
          conv_rhs => rw [pow_succ']

end PairwiseIndependence

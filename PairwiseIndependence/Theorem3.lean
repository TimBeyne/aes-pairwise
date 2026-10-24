import PairwiseIndependence.Pairwise.Definitions

/-!
# Theorem 3: two rounds of SHARK

The paper states Theorem 3 with `σ` the third singular value of the S-box
difference-distribution matrix `Dˢ`. By Lemma 7 that singular value equals
`‖Dˢ − U‖`, so the statement below takes a bound on `‖Dˢ − U‖` instead.

`‖·‖` on matrices is the Euclidean operator norm.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- Theorem 3 of the paper, for `Shark[n, q, S, L]` with `q` the size of the
alphabet `A`. The fixed S-box `S` enters `Dˢ` as a keyed family with a single
key (`Unit`). -/
def Theorem3 : Prop :=
  ∀ {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}
    (S : A ≃ A) (L : State A n ≃+ State A n), IsMDS L →
    4 ≤ Fintype.card A → 2 ≤ n →
    ∀ σ : ℝ, ‖differenceDistributionMatrix (fun (_ : Unit) (a : A) => S a) -
        uniformDifferenceDistributionMatrix A‖ ≤ σ →
    ∀ l : ℕ, 1 ≤ l → l ≤ n - 1 →
      let q := Fintype.card A
      let C (k : ℕ) : ℝ := (1 + 1 / (Real.sqrt q - 1)) ^ k * (Nat.choose (2 * n) k : ℝ) *
        ∑ i ∈ Finset.Icc 1 (k - 1), (Nat.choose (2 * n - k) (n - i) : ℝ) * 2 ^ i
      ‖differenceDistributionMatrix (sharkTwoCore S L) -
        uniformDifferenceDistributionMatrix (State A n)‖ ^ 2 ≤
        (2 / (Real.sqrt q - 1)) ^ (2 * n) +
          ∑ k ∈ Finset.Icc 2 l, C k * σ ^ (2 * k) / (Real.sqrt q - 1) ^ (2 * n - 2 * k) +
          (l + 2 : ℕ) * σ ^ (2 * (l + 1))

end PairwiseIndependence

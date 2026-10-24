import PairwiseIndependence.KeliherSui.Pair
import Mathlib.Data.Nat.Bitwise

/-!
# Packed support intersections for the Keliher--Sui calculation

Sixteen support indicators are stored in one integer. The finite lookup
table counts its set bits. The theorem below identifies the optimized
intersection calculation with the ordinary sum of support indicators;
packing changes neither the searched domain nor the numerical bound.
-/

namespace PairwiseIndependence

theorem keliherSui_ofFn_get {α : Type*} [Inhabited α] {n : Nat}
    (f : Fin n → α) (i : Fin n) : (Array.ofFn f)[i.val]! = f i := by
  simp

def keliherSuiPackBits : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => Nat.bit (p 0) (keliherSuiPackBits (fun i : Fin n => p i.succ))

theorem keliherSuiPackBits_lt {n : Nat} (p : Fin n → Bool) :
    keliherSuiPackBits p < 2 ^ n := by
  induction n with
  | zero => simp [keliherSuiPackBits]
  | succ n ih =>
    have h := ih (fun i : Fin n => p i.succ)
    simp only [keliherSuiPackBits, pow_succ]
    cases p 0 <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega

theorem keliherSuiPackBits_bit {n : Nat} (p : Fin n → Bool) (i : Fin n) :
    (keliherSuiPackBits p).testBit i.val = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [keliherSuiPackBits]
    · simpa only [keliherSuiPackBits, Fin.val_succ, Nat.testBit_bit_succ] using
        ih (fun k => p k.succ) j

def keliherSuiPackSupport (p : Fin 16 → Bool) : Nat := keliherSuiPackBits p

theorem keliherSuiPackSupport_lt :
    ∀ p : Fin 16 → Bool, keliherSuiPackSupport p < 65536 := by
  exact keliherSuiPackBits_lt

theorem keliherSuiPackSupport_bit :
    ∀ (p : Fin 16 → Bool) (i : Fin 16),
      (keliherSuiPackSupport p).testBit i.val = p i := by
  exact keliherSuiPackBits_bit

def keliherSuiBitCounts : Array Nat :=
  Array.ofFn (fun n : Fin 65536 =>
    ∑ i : Fin 16, if n.val.testBit i.val then 1 else 0)

theorem keliherSuiBitCounts_get (n : Fin 65536) :
    keliherSuiBitCounts[n.val]! =
      ∑ i : Fin 16, if n.val.testBit i.val then 1 else 0 := by
  simp [keliherSuiBitCounts]

theorem keliherSui_packed_intersection (p q : Fin 16 → Bool) :
    keliherSuiBitCounts[(keliherSuiPackSupport p &&&
      keliherSuiPackSupport q)]! =
      ∑ i : Fin 16, (if p i then 1 else 0) *
        (if q i then 1 else 0) := by
  have hn : keliherSuiPackSupport p &&& keliherSuiPackSupport q < 65536 :=
    Nat.and_le_left.trans_lt (keliherSuiPackSupport_lt p)
  rw [keliherSuiBitCounts_get ⟨_, hn⟩]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.testBit_and, keliherSuiPackSupport_bit, keliherSuiPackSupport_bit]
  cases p i <;> cases q i <;> decide

def keliherSuiPackedProfile (p : Fin 256 → Nat) : Array Nat :=
  Array.ofFn (fun j : Fin 16 => keliherSuiPackSupport
    (fun k : Fin 16 => decide (p (finProdFinEquiv (j, k)) ≠ 0)))

def keliherSuiPackedIntersection (bits p q : Array Nat) : Nat :=
  ∑ j : Fin 16, bits[(p[j.val]! &&& q[j.val]!)]!

/-- The fixed-size inner loop avoids allocating a mapped list for each
of the translated-pair checks. Its equality to the mathematical sum is
proved before the compiler is allowed to substitute it. -/
def keliherSuiPackedIntersectionFast (bits p q : Array Nat) : Nat :=
  let f := fun j : Nat => bits[(p[j]! &&& q[j]!)]!
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
    f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15

@[csimp] theorem keliherSuiPackedIntersection_eq_fast :
    keliherSuiPackedIntersection = keliherSuiPackedIntersectionFast := by
  funext bits p q
  simp [keliherSuiPackedIntersection, keliherSuiPackedIntersectionFast,
    Fin.sum_univ_succ, Nat.add_assoc]

theorem keliherSuiPackedIntersection_eq (p q : Fin 256 → Nat) :
    keliherSuiPackedIntersection keliherSuiBitCounts
      (keliherSuiPackedProfile p) (keliherSuiPackedProfile q) =
      ∑ t : Fin 256,
        keliherSuiCountSupport p t * keliherSuiCountSupport q t := by
  unfold keliherSuiPackedIntersection keliherSuiPackedProfile
  simp only [keliherSui_ofFn_get]
  simp_rw [keliherSui_packed_intersection]
  have h := Fintype.sum_equiv (finProdFinEquiv (m := 16) (n := 16))
    (fun jk => keliherSuiCountSupport p (finProdFinEquiv jk) *
      keliherSuiCountSupport q (finProdFinEquiv jk))
    (fun t => keliherSuiCountSupport p t * keliherSuiCountSupport q t)
    (fun _ => rfl)
  simpa [Fintype.sum_prod_type, keliherSuiCountSupport] using h

end PairwiseIndependence

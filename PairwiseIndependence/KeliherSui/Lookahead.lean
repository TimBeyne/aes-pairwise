import PairwiseIndependence.KeliherSui.FiveList

/-!
# A sorted-list-free form of the Keliher--Sui lookahead

Each nonzero AES byte difference-count row or column has exactly one entry
equal to four, with all other entries at most two. This proves the paper's
lookahead bound directly, without sorting the partial products. The proof
counts the possible coincidences of the exceptional count-four positions.
-/

namespace PairwiseIndependence

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Multiplicative factor contributed by a unique count-four position. -/
def keliherSuiHitMultiplier (specials : List T) (t : T) : Nat :=
  (specials.map (fun s => if t = s then 2 else 1)).prod

omit [Fintype T] in
theorem keliherSuiHitMultiplier_le_pow (specials : List T) (t : T) :
    keliherSuiHitMultiplier specials t ≤ 2 ^ specials.length := by
  induction specials with
  | nil => simp [keliherSuiHitMultiplier]
  | cons s rest ih =>
      simp only [keliherSuiHitMultiplier, List.map_cons, List.prod_cons,
        List.length_cons, pow_succ] at ih ⊢
      by_cases h : t = s
      · subst t
        simpa [mul_comm] using Nat.mul_le_mul_left 2 ih
      · simp [h]
        omega

/-- The weighted version of the integer lookahead. The sum of all extra
multipliers caused by coinciding count-four positions is at most
`2^m - 1` times the largest prefix weight. -/
theorem keliherSui_sum_hitMultiplier_le
    (w : T → Nat) (H : Nat) (hw : ∀ t, w t ≤ H)
    (specials : List T) :
    (∑ t : T, w t * keliherSuiHitMultiplier specials t) ≤
      (∑ t : T, w t) + (2 ^ specials.length - 1) * H := by
  induction specials with
  | nil => simp [keliherSuiHitMultiplier]
  | cons s rest ih =>
      have hsum :
          (∑ t : T, w t * keliherSuiHitMultiplier (s :: rest) t) =
            (∑ t : T, w t * keliherSuiHitMultiplier rest t) +
              w s * keliherSuiHitMultiplier rest s := by
        have hpoint (t : T) :
            w t * keliherSuiHitMultiplier (s :: rest) t =
              w t * keliherSuiHitMultiplier rest t +
                (if t = s then w t * keliherSuiHitMultiplier rest t else 0) := by
          by_cases h : t = s
          · simp [keliherSuiHitMultiplier, h]
            ring
          · simp [keliherSuiHitMultiplier, h]
        calc
          _ = ∑ t : T,
                ((w t * keliherSuiHitMultiplier rest t) +
                  (if t = s then w t * keliherSuiHitMultiplier rest t else 0)) := by
                    apply Finset.sum_congr rfl
                    intro t _
                    exact hpoint t
          _ = (∑ t : T, w t * keliherSuiHitMultiplier rest t) +
                w s * keliherSuiHitMultiplier rest s := by
                  rw [Finset.sum_add_distrib]
                  simp
      rw [hsum]
      have hmul :
          w s * keliherSuiHitMultiplier rest s ≤
            H * 2 ^ rest.length :=
        Nat.mul_le_mul (hw s) (keliherSuiHitMultiplier_le_pow rest s)
      have hpow : 1 ≤ 2 ^ rest.length :=
        pow_pos (by decide : 0 < (2 : Nat)) _
      have hidentity :
          (2 ^ rest.length * 2 - 1) * H =
            (2 ^ rest.length - 1) * H + H * 2 ^ rest.length := by
        have hp : 2 ^ rest.length * 2 - 1 =
            (2 ^ rest.length - 1) + 2 ^ rest.length := by omega
        rw [hp, add_mul]
        ac_rfl
      simp only [List.length_cons, pow_succ]
      calc
        _ ≤ ((∑ t : T, w t) + (2 ^ rest.length - 1) * H) +
              H * 2 ^ rest.length := Nat.add_le_add ih hmul
        _ = (∑ t : T, w t) + (2 ^ rest.length * 2 - 1) * H := by
          rw [hidentity]
          omega

/-- A list of remaining byte profiles, each paired with its unique
count-four coordinate. -/
def keliherSuiProfileProduct (profiles : List ((T → Nat) × T)) (t : T) : Nat :=
  (profiles.map (fun p => p.1 t)).prod

omit [Fintype T] in
theorem keliherSui_profileProduct_le
    (profiles : List ((T → Nat) × T))
    (hprofile : ∀ p ∈ profiles, ∀ t,
      p.1 t ≤ 2 * (if t = p.2 then 2 else 1))
    (t : T) :
    keliherSuiProfileProduct profiles t ≤
      2 ^ profiles.length *
        keliherSuiHitMultiplier (profiles.map Prod.snd) t := by
  induction profiles with
  | nil => simp [keliherSuiProfileProduct, keliherSuiHitMultiplier]
  | cons p rest ih =>
      have hp := hprofile p (by simp) t
      have hrest : ∀ q ∈ rest, ∀ t,
          q.1 t ≤ 2 * (if t = q.2 then 2 else 1) := by
        intro q hq t
        exact hprofile q (by simp [hq]) t
      have hi := ih hrest
      calc
        keliherSuiProfileProduct (p :: rest) t =
            p.1 t * keliherSuiProfileProduct rest t := by
              simp [keliherSuiProfileProduct]
        _ ≤ (2 * (if t = p.2 then 2 else 1)) *
              (2 ^ rest.length *
                keliherSuiHitMultiplier (rest.map Prod.snd) t) :=
              Nat.mul_le_mul hp hi
        _ = 2 ^ (p :: rest).length *
              keliherSuiHitMultiplier ((p :: rest).map Prod.snd) t := by
              simp [keliherSuiHitMultiplier, pow_succ]
              ring_nf

/-- The exact integer upper bound used by the pruning search. If `m`
factors remain, `S` is the sum of current prefix weights and `H` bounds
their maximum, then the completed five-list is at most
`2^m * (S + (2^m - 1) * H)`. -/
theorem keliherSui_lookahead_le
    (w : T → Nat) (H : Nat) (hw : ∀ t, w t ≤ H)
    (profiles : List ((T → Nat) × T))
    (hprofile : ∀ p ∈ profiles, ∀ t,
      p.1 t ≤ 2 * (if t = p.2 then 2 else 1)) :
    (∑ t : T, w t * keliherSuiProfileProduct profiles t) ≤
      2 ^ profiles.length *
        ((∑ t : T, w t) + (2 ^ profiles.length - 1) * H) := by
  have hterm (t : T) :
      w t * keliherSuiProfileProduct profiles t ≤
        2 ^ profiles.length *
          (w t * keliherSuiHitMultiplier (profiles.map Prod.snd) t) := by
    have hp := keliherSui_profileProduct_le profiles hprofile t
    calc
      _ ≤ w t * (2 ^ profiles.length *
          keliherSuiHitMultiplier (profiles.map Prod.snd) t) :=
        Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  calc
    _ ≤ ∑ t : T,
          2 ^ profiles.length *
            (w t * keliherSuiHitMultiplier (profiles.map Prod.snd) t) :=
      Finset.sum_le_sum (fun t _ => hterm t)
    _ = 2 ^ profiles.length *
          (∑ t : T, w t *
            keliherSuiHitMultiplier (profiles.map Prod.snd) t) := by
      rw [Finset.mul_sum]
    _ ≤ 2 ^ profiles.length *
          ((∑ t : T, w t) + (2 ^ profiles.length - 1) * H) := by
      have h := keliherSui_sum_hitMultiplier_le w H hw
        (profiles.map Prod.snd)
      simpa using Nat.mul_le_mul_left (2 ^ profiles.length) h

/-- The concrete AES byte difference count, using numeric byte indices
for the finite pruning calculation. -/
def aesSboxDifferenceCountFin (a b : Fin 256) : Nat :=
  aesSboxDifferenceCount (aesByteOfNat a.val) (aesByteOfNat b.val)

/-- Reindex the stored inverse-byte count table by the AES output affine
permutation. This keeps the finite profile check on the precomputed table. -/
theorem aesSboxDifferenceCountFin_index (a b : Fin 256) :
    aesSboxDifferenceCountFin a b =
      (aesInverseDifferenceCountTable[a.val]!)[
        (aesInverseAffineDifferenceIndex b).val]! := by
  simp only [aesSboxDifferenceCountFin, aesSboxDifferenceCount,
    aesByteToNat_ofNat]
  rfl

end PairwiseIndependence

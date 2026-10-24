import PairwiseIndependence.KeliherSui.ScalarCertificate

namespace PairwiseIndependence

theorem keliherSui_profile_bound {T : Type*} [DecidableEq T]
    (p : T → Nat) (s : T)
    (hv : ∀ t, p t = 0 ∨ p t = 2 ∨ p t = 4)
    (hs : ∀ t, p t = 4 ↔ t = s) (t : T) :
    p t ≤ 2 * (if t = s then 2 else 1) := by
  by_cases h : t = s
  · simp [h, (hs s).2 rfl]
  · rcases hv t with h0 | h2 | h4
    · simp [h, h0]
    · simp [h, h2]
    · exact False.elim (h ((hs t).1 h4))

theorem keliherSui_pair_bound {T : Type*} [DecidableEq T]
    (p q : T → Nat) (sp sq : T)
    (hp : ∀ t, p t ≤ 2 * (if t = sp then 2 else 1))
    (hq : ∀ t, q t ≤ 2 * (if t = sq then 2 else 1)) (t : T) :
    p t * q t ≤ if sp = sq then 16 else 8 := by
  have h := Nat.mul_le_mul (hp t) (hq t)
  split_ifs with heq
  · by_cases hts : t = sp <;> by_cases htq : t = sq <;> simp_all; omega
  · by_cases hts : t = sp <;> by_cases htq : t = sq <;> simp_all; omega

/-- Any pruned pair bounds the full product of five profiles. The other
three need only their unique count-four profile, as in the paper's
lookahead step. -/
theorem keliherSui_five_product_le_of_pair
    (p : Fin 5 → Fin 256 → Nat) (special : Fin 5 → Fin 256)
    (hp : ∀ i t, p i t ≤ 2 * (if t = special i then 2 else 1))
    (i j : Fin 5) (hij : i ≠ j)
    (hbound : 8 * ((∑ t : Fin 256, p i t * p j t) +
      7 * (if special i = special j then 16 else 8)) ≤ 3392) :
    (∑ t : Fin 256, ∏ k : Fin 5, p k t) ≤ 3392 := by
  classical
  let rest : Finset (Fin 5) := (Finset.univ.erase i).erase j
  let profiles : List ((Fin 256 → Nat) × Fin 256) :=
    rest.toList.map (fun k => (p k, special k))
  have hlen : profiles.length = 3 := by
    simp [profiles, rest, Ne.symm hij]
  have hprofile : ∀ r ∈ profiles, ∀ t,
      r.1 t ≤ 2 * (if t = r.2 then 2 else 1) := by
    intro r hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    exact hp k
  have hproduct (t : Fin 256) :
      keliherSuiProfileProduct profiles t = ∏ k ∈ rest, p k t := by
    simp [keliherSuiProfileProduct, profiles, List.map_map]
  have hsplit (t : Fin 256) :
      (∏ k : Fin 5, p k t) = p i t * p j t * ∏ k ∈ rest, p k t := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr
      ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    simp only [rest, mul_assoc]
  have hlook := keliherSui_lookahead_le (fun t => p i t * p j t)
    (if special i = special j then 16 else 8)
    (keliherSui_pair_bound (p i) (p j) (special i) (special j) (hp i) (hp j))
    profiles hprofile
  rw [hlen] at hlook
  norm_num at hlook hbound
  simpa only [hproduct, hsplit] using hlook.trans hbound

end PairwiseIndependence

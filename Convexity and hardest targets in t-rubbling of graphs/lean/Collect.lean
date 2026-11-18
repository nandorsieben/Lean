import Finite

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

/-- Two available source pebbles can be selected from any list of mass at least two. -/
theorem exists_sources (L : List α) (hn : L.Nodup) (p : Distribution α)
    (h : 2 ≤ sumOn L p) :
    ∃ u ∈ L, ∃ v ∈ L,
      ∀ x, (if x = u then 1 else 0) + (if x = v then 1 else 0) ≤ p x := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    obtain ⟨ha, hL⟩ := List.nodup_cons.mp hn
    by_cases htwo : 2 ≤ p a
    · refine ⟨a, by simp, a, by simp, ?_⟩
      intro x
      by_cases hx : x = a
      · subst x; simp; omega
      · simp [hx]
    · by_cases hone : 1 ≤ p a
      · have htail : 0 < sumOn L p := by rw [sumOn_cons] at h; omega
        obtain ⟨v, hv, hpv⟩ := sumOn_pos L p htail
        have hav : a ≠ v := by intro heq; subst v; exact ha hv
        refine ⟨a, by simp, v, by simp [hv], ?_⟩
        intro x
        by_cases hx : x = a
        · subst x; simpa [hav] using hone
        · by_cases hy : x = v
          · subst x; simp [Ne.symm hav]; omega
          · simp [hx, hy]
      · have htail : 2 ≤ sumOn L p := by rw [sumOn_cons] at h; omega
        obtain ⟨u, hu, v, hv, hp⟩ := ih hL htail
        exact ⟨u, by simp [hu], v, by simp [hv], hp⟩

/-- Pool a whole set of neighbors into a common destination by legal moves.
Every vertex outside the source set and destination keeps its original count. -/
theorem collect_pairs {adj : α → α → Prop} (L : List α) (hn : L.Nodup)
    (z : α) (hz : z ∉ L) (hadj : ∀ x ∈ L, adj x z) (p : Distribution α) :
    ∃ q, Reachable adj p q ∧ q z = p z + sumOn L p / 2 ∧
      sumOn L q = sumOn L p % 2 ∧
      (∀ x, x ∉ L → x ≠ z → q x = p x) := by
  by_cases hsmall : sumOn L p < 2
  · refine ⟨p, Reachable.refl p, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro x _ _; rfl
  · obtain ⟨u, hu, v, hv, havail⟩ := exists_sources L hn p (by omega)
    let p' := fire p u v z
    have hm : LegalMove adj p p' := fire_legal p u v z (hadj u hu) (hadj v hv) havail
    have hb : ∀ x, p' x + (if x = u then 1 else 0) + (if x = v then 1 else 0) =
        p x + (if x = z then 1 else 0) := by
      intro x
      have hx := havail x
      dsimp only [p', fire]
      omega
    have hmass : sumOn L p' + 2 = sumOn L p := by
      have hh := sumOn_balance L hn hb
      simpa [hu, hv, hz, Nat.add_assoc] using hh
    have hzu : z ≠ u := by intro h; subst u; exact hz hu
    have hzv : z ≠ v := by intro h; subst v; exact hz hv
    have hpz : p' z = p z + 1 := by simp [p', fire, hzu, hzv]
    obtain ⟨q, hpq, hqz, hmassq, hother⟩ := collect_pairs L hn z hz hadj p'
    refine ⟨q, (Reachable.tail (Reachable.refl p) hm).trans hpq, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro x hx hxe
      rw [hother x hx hxe]
      have hxu : x ≠ u := by intro h; subst u; exact hx hu
      have hxv : x ≠ v := by intro h; subst v; exact hx hv
      simp [p', fire, hxu, hxv, hxe]
termination_by sumOn L p
decreasing_by
  simp only [p'] at *
  omega

end RubblingFamily

#print axioms RubblingFamily.collect_pairs

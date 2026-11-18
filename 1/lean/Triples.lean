import Collect

namespace RubblingFamily
variable {α : Type} [DecidableEq α] {adj : α → α → Prop}

/-- Three distinct occupied vertices exist when a singleton distribution has mass three. -/
theorem three_singletons (S : List α) (hn : S.Nodup) (p : Distribution α)
    (hs : ∀ x ∈ S, p x ≤ 1) (hm : 3 ≤ sumOn S p) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p a = 1 ∧ p b = 1 ∧ p c = 1 := by
  induction S with
  | nil => simp at hm
  | cons a S ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have hpa := hs a (by simp)
    have hst : ∀ x ∈ S, p x ≤ 1 := by intro x hx; exact hs x (by simp [hx])
    by_cases hp : p a = 0
    · have hmass : 3 ≤ sumOn S p := by rw [sumOn_cons] at hm; omega
      obtain ⟨b, hb, c, hc, d, hd, hbc, hbd, hcd, hpb, hpc, hpd⟩ := ih ht hst hmass
      exact ⟨b, by simp [hb], c, by simp [hc], d, by simp [hd],
        hbc, hbd, hcd, hpb, hpc, hpd⟩
    · have hmass : 2 ≤ sumOn S p := by rw [sumOn_cons] at hm; omega
      obtain ⟨b, hb, c, hc, havail⟩ := exists_sources S ht p hmass
      have hbc : b ≠ c := by
        intro heq; subst c
        have h := havail b
        simp only [↓reduceIte] at h
        have hh := hst b hb
        omega
      have hpb := havail b
      have hpc := havail c
      simp only [hbc, Ne.symm hbc, ↓reduceIte, Nat.add_zero, Nat.zero_add] at hpb hpc
      have hb1 := hst b hb
      have hc1 := hst c hc
      refine ⟨a, by simp, b, by simp [hb], c, by simp [hc],
        ?_, ?_, hbc, by omega, by omega, by omega⟩
      · intro h; subst b; exact ha hb
      · intro h; subst c; exact ha hc

/-- A clique of singletons sends one pebble to its designated sinks per triple. -/
theorem collect_triples (S N : List α) (hS : S.Nodup) (hN : N.Nodup)
    (hdis : ∀ x ∈ S, x ∉ N) (sink : α → α)
    (hsink : ∀ x ∈ S, sink x ∈ N) (hadj : ∀ x ∈ S, adj x (sink x))
    (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj x y)
    (p : Distribution α) (hs : ∀ x ∈ S, p x ≤ 1) :
    ∃ q, Reachable adj p q ∧ (∀ x ∈ S, q x ≤ 1) ∧
      sumOn S q = sumOn S p % 3 ∧
      sumOn N q = sumOn N p + sumOn S p / 3 ∧
      (∀ x, x ∉ S → x ∉ N → q x = p x) := by
  by_cases hm : 3 ≤ sumOn S p
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hpa, hpb, hpc⟩ :=
      three_singletons S hS p hs hm
    have hsc := hsink c hc
    have hcN := hdis c hc
    have hcs : c ≠ sink c := by intro h; exact hcN (h ▸ hsc)
    have has : a ≠ sink c := by intro h; exact hdis a ha (h ▸ hsc)
    have hbs : b ≠ sink c := by intro h; exact hdis b hb (h ▸ hsc)
    let p1 := fire p a b c
    have hp1 : LegalMove adj p p1 :=
      fire_legal_distinct p a b c (hclique a ha c hc hac)
        (hclique b hb c hc hbc) hab (by omega) (by omega)
    have hp1c : p1 c = 2 := by simp [p1, fire, Ne.symm hac, Ne.symm hbc, hpc]
    let p2 := transfer p1 c (sink c) 1
    have hp2 : Reachable adj p1 p2 :=
      transfer_reachable p1 c (sink c) (hadj c hc) hcs 1 (by omega)
    have hp2point : ∀ x, p2 x =
        if x = a ∨ x = b ∨ x = c then 0
        else p x + (if x = sink c then 1 else 0) := by
      intro x
      by_cases hxa : x = a
      · subst x; simp [p2, transfer, p1, fire, hab, hac, has, hpa]
      · by_cases hxb : x = b
        · subst x; simp [p2, transfer, p1, fire, Ne.symm hab, hbc, hbs, hpb]
        · by_cases hxc : x = c
          · subst x; simp [p2, transfer, hp1c, hxa, hxb]
          · by_cases hxs : x = sink c
            · subst x; simp [p2, transfer, p1, fire, Ne.symm has, Ne.symm hbs, Ne.symm hcs]
            · simp [p2, transfer, p1, fire, hxa, hxb, hxc, hxs]
    have hsingle : ∀ x ∈ S, p2 x ≤ 1 := by
      intro x hx
      rw [hp2point]
      split
      · omega
      · have hxs : x ≠ sink c := by intro h; exact hdis x hx (h ▸ hsc)
        simpa [hxs] using hs x hx
    have hmass : sumOn S p2 + 3 = sumOn S p := by
      have heq : ∀ x ∈ S,
          p2 x + ((if x=a then 1 else 0) + (if x=b then 1 else 0) +
            (if x=c then 1 else 0)) = p x := by
        intro x hx
        rw [hp2point]
        by_cases hxa : x = a
        · subst x; simp [hab, hac, hpa]
        · by_cases hxb : x = b
          · subst x; simp [Ne.symm hab, hbc, hpb]
          · by_cases hxc : x = c
            · subst x; simp [hxa, hxb, hpc]
            · have hxs : x ≠ sink c := by intro h; exact hdis x hx (h ▸ hsc)
              simp [hxa, hxb, hxc, hxs]
      have hh := sumOn_congr S _ _ heq
      simpa only [sumOn_add, sumOn_indicator S hS, ha, hb, hc, ↓reduceIte] using hh
    have hNmass : sumOn N p2 = sumOn N p + 1 := by
      apply sumOn_single_change N S hN (sink c) hsc
        (by intro x hx hxS; exact hdis x hxS hx) p p2 1
      · rw [hp2point]; simp [Ne.symm has, Ne.symm hbs, Ne.symm hcs]
      · intro x hxS hxs
        rw [hp2point]
        have hxa : x ≠ a := by intro h; exact hxS (h ▸ ha)
        have hxb : x ≠ b := by intro h; exact hxS (h ▸ hb)
        have hxc : x ≠ c := by intro h; exact hxS (h ▸ hc)
        simp [hxa, hxb, hxc, hxs]
    obtain ⟨q, hpq, hqs, hqmass, hqN, hqo⟩ :=
      collect_triples S N hS hN hdis sink hsink hadj hclique p2 hsingle
    refine ⟨q, (Reachable.tail (.refl p) hp1).trans (hp2.trans hpq), hqs, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro x hxS hxN
      rw [hqo x hxS hxN, hp2point]
      have hxa : x ≠ a := by intro h; exact hxS (h ▸ ha)
      have hxb : x ≠ b := by intro h; exact hxS (h ▸ hb)
      have hxc : x ≠ c := by intro h; exact hxS (h ▸ hc)
      have hxs : x ≠ sink c := by intro h; exact hxN (h ▸ hsc)
      simp [hxa, hxb, hxc, hxs]
  · exact ⟨p, .refl p, hs, by omega, by omega, by simp⟩
termination_by sumOn S p
decreasing_by
  dsimp only [p2, p1] at *
  omega

end RubblingFamily
#print axioms RubblingFamily.collect_triples

import Family

namespace RubblingFamily

def inVI {m n : Nat} : Vertex m n → Prop
  | .v i => m≤i.val
  | _ => False

/-- Comparing the two excesses identifies actual hardest targets. -/
theorem hardest_by_excess {m n : Nat} (hm : 1≤m) (hn : 2≤n) (t : Nat) (ht : 1≤t)
    (hW : 1<min (2*t) ((m+n+1)/3)) (hV : 1<min (4*t) (n/2))
    (r : Vertex m n) :
    IsHardestTarget m n t r ↔
      (r=.w ∧ min (4*t) (n/2)≤min (2*t) ((m+n+1)/3)) ∨
      (inVI r ∧ min (2*t) ((m+n+1)/3)≤min (4*t) (n/2)) := by
  rw [hardest_iff_value hm hn t ht]
  cases r with
  | w =>
    simp only [targetValue,inVI,true_and,false_and,or_false]
    unfold proposedValue
    omega
  | u i =>
    by_cases hic : i.val<m <;> simp [targetValue,hic,inVI,proposedValue]
    all_goals omega
  | v i =>
    by_cases hic : i.val<m <;> simp [targetValue,hic,inVI,proposedValue]
    all_goals omega

/-- Proposition 4.1, in the paper's order and H_t^rho notation. -/
theorem hardest_target_regimes {m n : Nat} (hm : 1≤m) (hn : 6≤n)
    (hk : 3*(n/2)+2≤m+n) (t : Nat) (ht : 1≤t) (r : Vertex m n) :
    (n<4*t → (Hρ m n t r ↔ r=.w)) ∧
    ((4*t≤n ∧ n≤4*t+1) → (Hρ m n t r ↔ r=.w ∨ inVI r)) ∧
    (4*t+1<n → (Hρ m n t r ↔ inVI r)) := by
  have hW : 1<min (2*t) ((m+n+1)/3) := by omega
  have hV : 1<min (4*t) (n/2) := by omega
  have h := hardest_by_excess hm (by omega) t ht hW hV r
  obtain ⟨hpre,htie,hpost⟩ := hardest_target_comparison m n t hn hk ht
  refine ⟨?_,?_,?_⟩
  · intro hb
    have hh := hpost hb
    change IsHardestTarget m n t r ↔ r=.w
    rw [h]
    constructor
    · intro hh'; rcases hh' with hh' | hh'
      · exact hh'.1
      · omega
    · intro hh'; exact Or.inl ⟨hh',by omega⟩
  · intro hb
    have hh := htie (by omega)
    change IsHardestTarget m n t r ↔ r=.w ∨ inVI r
    rw [h]
    simp only [hh,Nat.le_refl,and_true]
  · intro hb
    have hh := hpre hb
    change IsHardestTarget m n t r ↔ inVI r
    rw [h]
    constructor
    · intro hh'; rcases hh' with hh' | hh' <;> simp_all <;> omega
    · intro hh'; exact Or.inr ⟨hh',by omega⟩

theorem GraphNumberIs.unique {α : Type} [DecidableEq α]
    {adj : α→α→Prop} {size : Distribution α→Nat} {t R S : Nat}
    (hR : GraphNumberIs adj size t R) (hS : GraphNumberIs adj size t S) : R=S := by
  by_cases h : R<S
  · exact False.elim (hS.2 R h hR.1)
  · by_cases h' : S<R
    · exact False.elim (hR.2 S h' hS.1)
    · omega

/-- The five claimed numbers are certified as actual graph rubbling numbers. -/
theorem graph_example_values :
    GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize 1 8 ∧
    GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize 2 15 ∧
    GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize 3 19 ∧
    GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize 4 24 ∧
    GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize 5 28 := by
  exact ⟨family_number (by decide) (by decide) 1 (by decide),
    family_number (by decide) (by decide) 2 (by decide),
    family_number (by decide) (by decide) 3 (by decide),
    family_number (by decide) (by decide) 4 (by decide),
    family_number (by decide) (by decide) 5 (by decide)⟩

/-- Any sequence of the graph's rubbling numbers violates both midpoint inequalities. -/
theorem graph_nonconvex_nonconcave (ρ : Nat→Nat)
    (hρ : ∀t, 1≤t → GraphNumberIs (familyAdj (m:=9) (n:=14)) familySize t (ρ t)) :
    ρ 1+ρ 3<2*ρ 2 ∧ 2*ρ 3<ρ 2+ρ 4 := by
  obtain ⟨h1,h2,h3,h4,_⟩ := graph_example_values
  have h1' := (hρ 1 (by decide)).unique h1
  have h2' := (hρ 2 (by decide)).unique h2
  have h3' := (hρ 3 (by decide)).unique h3
  have h4' := (hρ 4 (by decide)).unique h4
  omega

/-- An additional graph-number formula for G(5,6), for every positive t. -/
theorem graph_5_6 (t : Nat) (ht : 1≤t) :
    GraphNumberIs (familyAdj (m:=5) (n:=6)) familySize t
      (if t=1 then 7 else 4*t+4) := by
  have h := family_number (m:=5) (n:=6) (by decide) (by decide) t ht
  have he : proposedValue 5 6 t=(if t=1 then 7 else 4*t+4) := by
    unfold proposedValue
    by_cases ht1 : t=1 <;> simp [ht1] <;> omega
  rw [he] at h
  exact h

/-- Example 5.1: the exact hardest-target sets for every positive demand. -/
theorem graph_5_6_targets (r : Vertex 5 6) :
    (Hρ 5 6 1 r ↔ inVI r) ∧
    (∀ t, 2≤t → (Hρ 5 6 t r ↔ r=.w)) := by
  constructor
  · have h := hardest_target_regimes (m:=5) (n:=6)
      (by decide) (by decide) (by decide) 1 (by decide) r
    exact h.2.2 (by decide)
  · intro t ht
    have h := hardest_target_regimes (m:=5) (n:=6)
      (by decide) (by decide) (by decide) t (by omega) r
    exact h.1 (by omega)

/-- Example 5.1: the intersection of H_t^rho(G(5,6)) over positive t is empty. -/
theorem graph_5_6_no_common_target :
    ¬ ∃ r : Vertex 5 6, ∀ t, 1≤t → Hρ 5 6 t r := by
  intro ⟨r,hr⟩
  obtain ⟨hfirst,hlater⟩ := graph_5_6_targets r
  have hVI := hfirst.mp (hr 1 (by decide))
  have hw := (hlater 2 (by decide)).mp (hr 2 (by decide))
  subst r
  exact hVI

/-- The hardest-target comparison stated in Example 5.3. -/
theorem graph_example_targets (r : Vertex 9 14) :
    (Hρ 9 14 3 r ↔ inVI r) ∧ (Hρ 9 14 4 r ↔ r=.w) := by
  have h3 := hardest_target_regimes (m:=9) (n:=14)
    (by decide) (by decide) (by decide) 3 (by decide) r
  have h4 := hardest_target_regimes (m:=9) (n:=14)
    (by decide) (by decide) (by decide) 4 (by decide) r
  exact ⟨h3.2.2 (by decide),h4.1 (by decide)⟩

/-- Example 5.2: a strict change after any prescribed positive h. -/
theorem arbitrarily_late_switch (h : Nat) (hh : 1≤h) (t : Nat) (ht : 1≤t)
    (r : Vertex (2*h+3) (4*h+2)) :
    (t≤h → (Hρ (2*h+3) (4*h+2) t r ↔ inVI r)) ∧
    (h+1≤t → (Hρ (2*h+3) (4*h+2) t r ↔ r=.w)) := by
  have hn : 6≤4*h+2 := by omega
  have hk : 3*((4*h+2)/2)+2≤(2*h+3)+(4*h+2) := by omega
  obtain ⟨hpost,_,hpre⟩ := hardest_target_regimes (by omega) hn hk t ht r
  exact ⟨fun hb => hpre (by omega),fun hb => hpost (by omega)⟩

end RubblingFamily
#print axioms RubblingFamily.hardest_target_regimes
#print axioms RubblingFamily.graph_example_values
#print axioms RubblingFamily.graph_nonconvex_nonconcave
#print axioms RubblingFamily.arbitrarily_late_switch
#print axioms RubblingFamily.graph_5_6_targets
#print axioms RubblingFamily.graph_5_6_no_common_target
#print axioms RubblingFamily.graph_example_targets

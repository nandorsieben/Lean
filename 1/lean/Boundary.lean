import Routing

namespace RubblingFamily

abbrev P3Vertex := Vertex 0 1

private theorem fin_one_zero (i : Fin 1) : i = 0 := Fin.ext (by omega)

theorem p3_size (p : Distribution P3Vertex) :
    familySize p = p .w + p (.u 0) + p (.v 0) := by
  simp [familySize, List.ofFn_succ]

def pile {α : Type} [DecidableEq α] (v : α) (k : Nat) : Distribution α :=
  fun x => if x = v then k else 0

def p3WeightLeft (p : Distribution P3Vertex) := 4 * p .w + 2 * p (.u 0) + p (.v 0)
def p3WeightMiddle (p : Distribution P3Vertex) := p .w + 2 * p (.u 0) + p (.v 0)
def p3WeightRight (p : Distribution P3Vertex) := p .w + 2 * p (.u 0) + 4 * p (.v 0)

/-- Every legal move, including a strict move, respects the endpoint weight. -/
theorem p3WeightLeft_move {p q : Distribution P3Vertex}
    (h : LegalMove familyAdj p q) : p3WeightLeft q ≤ p3WeightLeft p := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := h
  have hw := hb .w
  have hU := hb (.u 0)
  have hV := hb (.v 0)
  cases u <;> cases v <;> cases z <;>
    simp_all [familyAdj, fin_one_zero, p3WeightLeft] <;> omega

theorem p3WeightMiddle_move {p q : Distribution P3Vertex}
    (h : LegalMove familyAdj p q) : p3WeightMiddle q ≤ p3WeightMiddle p := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := h
  have hw := hb .w
  have hU := hb (.u 0)
  have hV := hb (.v 0)
  cases u <;> cases v <;> cases z <;>
    simp_all [familyAdj, fin_one_zero, p3WeightMiddle] <;> omega

theorem p3WeightRight_move {p q : Distribution P3Vertex}
    (h : LegalMove familyAdj p q) : p3WeightRight q ≤ p3WeightRight p := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := h
  have hw := hb .w
  have hU := hb (.u 0)
  have hV := hb (.v 0)
  cases u <;> cases v <;> cases z <;>
    simp_all [familyAdj, fin_one_zero, p3WeightRight] <;> omega

/-- The P_3 left endpoint upper bound, proved by explicit legal transfers. -/
theorem p3_upper_w (t : Nat) :
    TargetUpperBound (familyAdj (m := 0) (n := 1)) familySize .w t (4 * t) := by
  intro p hp
  obtain ⟨q, hseq, hq⟩ := path_delivers (adj := familyAdj) p
    (.w : P3Vertex) (.u 0) (.v 0) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [p3_size] at hp
  refine ⟨q, hseq, ?_⟩
  omega

theorem p3_upper_middle (t : Nat) :
    TargetUpperBound (familyAdj (m := 0) (n := 1)) familySize (.u 0) t (2 * t) := by
  intro p hp
  obtain ⟨q, hseq, hq⟩ := two_neighbors_deliver (adj := familyAdj) p
    (.w : P3Vertex) (.u 0) (.v 0) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [p3_size] at hp
  refine ⟨q, hseq, ?_⟩
  omega

theorem p3_upper_v (t : Nat) :
    TargetUpperBound (familyAdj (m := 0) (n := 1)) familySize (.v 0) t (4 * t) := by
  intro p hp
  obtain ⟨q, hseq, hq⟩ := path_delivers (adj := familyAdj) p
    (.v 0 : P3Vertex) (.u 0) .w (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [p3_size] at hp
  refine ⟨q, hseq, ?_⟩
  omega

/-- An actual target rubbling formula, quantified over every positive t. -/
theorem p3_target_w (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs (familyAdj (m := 0) (n := 1)) familySize .w t (4 * t) := by
  apply target_number_of_bounds (p3_upper_w t)
  refine ⟨pile (.v 0) (4 * t - 1), ?_, ?_⟩
  · rw [p3_size]; simp only [pile, reduceCtorEq, ↓reduceIte]; omega
  · apply not_t_reachable_of_weight (W := p3WeightLeft) (C := 4)
      p3WeightLeft_move
    · intro q; unfold p3WeightLeft; omega
    · simp only [p3WeightLeft, pile, reduceCtorEq, ↓reduceIte]; omega

theorem p3_target_middle (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs (familyAdj (m := 0) (n := 1)) familySize (.u 0) t (2 * t) := by
  apply target_number_of_bounds (p3_upper_middle t)
  refine ⟨pile .w (2 * t - 1), ?_, ?_⟩
  · rw [p3_size]; simp only [pile, reduceCtorEq, ↓reduceIte]; omega
  · apply not_t_reachable_of_weight (W := p3WeightMiddle) (C := 2)
      p3WeightMiddle_move
    · intro q; unfold p3WeightMiddle; omega
    · simp only [p3WeightMiddle, pile, reduceCtorEq, ↓reduceIte]; omega

theorem p3_target_v (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs (familyAdj (m := 0) (n := 1)) familySize (.v 0) t (4 * t) := by
  apply target_number_of_bounds (p3_upper_v t)
  refine ⟨pile .w (4 * t - 1), ?_, ?_⟩
  · rw [p3_size]; simp only [pile, reduceCtorEq, ↓reduceIte]; omega
  · apply not_t_reachable_of_weight (W := p3WeightRight) (C := 4)
      p3WeightRight_move
    · intro q; unfold p3WeightRight; omega
    · simp only [p3WeightRight, pile, reduceCtorEq, ↓reduceIte]; omega

end RubblingFamily

#print axioms RubblingFamily.p3_target_w
#print axioms RubblingFamily.p3_target_middle
#print axioms RubblingFamily.p3_target_v

import TwoFar
import Frozen

namespace RubblingFamily

/-- The paper's F1: the other independent U vertices. -/
def uiFar1 {m n : Nat} (i : Fin (m + n)) : Vertex m n → Bool
  | .u j => decide (j ≠ i ∧ m ≤ j.val)
  | _ => false

/-- The paper's F2: all V vertices except the matched neighbor. -/
def uiFar2 {m n : Nat} (i : Fin (m + n)) : Vertex m n → Bool
  | .v j => decide (j ≠ i)
  | _ => false

def uiNearVertices {m n : Nat} (i : Fin (m + n)) : List (Vertex m n) :=
  (vertices m n).filter fun x => decide (familyAdj x (.u i))
def uiFar1Vertices {m n : Nat} (i : Fin (m + n)) : List (Vertex m n) :=
  (vertices m n).filter (uiFar1 i)
def uiFar2Vertices {m n : Nat} (i : Fin (m + n)) : List (Vertex m n) :=
  (vertices m n).filter (uiFar2 i)

theorem ui_partition {m n : Nat} (i : Fin (m + n)) (hi : m ≤ i.val)
    (p : Distribution (Vertex m n)) :
    familySize p = p (.u i) + sumOn (uiNearVertices i) p +
      sumOn (uiFar1Vertices i) p + sumOn (uiFar2Vertices i) p := by
  have hilt : ¬ i.val < m := by omega
  have hpoint : ∀ x ∈ vertices m n, p x =
      (if x = .u i then p (.u i) else 0) +
      (if decide (familyAdj x (.u i)) then p x else 0) +
      (if uiFar1 i x then p x else 0) + (if uiFar2 i x then p x else 0) := by
    intro x _
    cases x with
    | w => simp [familyAdj, uiFar1, uiFar2]
    | u j =>
      by_cases hji : j = i
      · subst j; simp [familyAdj, uiFar1, uiFar2]
      · by_cases hj : j.val < m
        · have hjge : ¬ m ≤ j.val := by omega
          simp [familyAdj, uiFar1, uiFar2, hji, hj, hilt, hjge]
        · have hjge : m ≤ j.val := by omega
          simp [familyAdj, uiFar1, uiFar2, hji, hj, hilt, hjge]
    | v j => by_cases hji : j = i <;> simp [familyAdj, uiFar1, uiFar2, hji]
  have hh := sumOn_congr (vertices m n) _ _ hpoint
  rw [sumOn_add, sumOn_add, sumOn_add, sumOn_indicator _ (vertices_nodup m n)] at hh
  rw [← sumOn_vertices p]
  unfold uiNearVertices uiFar1Vertices uiFar2Vertices
  rw [sumOn_bool_filter, sumOn_bool_filter, sumOn_bool_filter]
  simpa only [mem_vertices, ↓reduceIte] using hh

/-- Case (c) upper bound, now with its routing construction proved. -/
theorem ui_upper {m n : Nat} (i : Fin (m + n)) (hi : m ≤ i.val) (t : Nat) :
    TargetUpperBound familyAdj familySize (.u i) t (4 * t + 1) := by
  have hilt : ¬ i.val < m := by omega
  apply two_far_upper (uiNearVertices i) (uiFar1Vertices i) (uiFar2Vertices i)
    (List.Pairwise.filter _ (vertices_nodup m n))
    (List.Pairwise.filter _ (vertices_nodup m n))
    (List.Pairwise.filter _ (vertices_nodup m n)) (.u i) .w (.v i)
  · simp [uiNearVertices, familyAdj]
  · simp [uiFar1Vertices, uiFar1]
  · simp [uiFar2Vertices, uiFar2]
  · simp [uiNearVertices, mem_vertices, familyAdj]
  · simp [uiNearVertices, mem_vertices, familyAdj]
  · intro x hx hf
    cases x <;> simp_all [uiNearVertices, uiFar1Vertices, uiFar1, familyAdj] <;> omega
  · intro x hx hf
    cases x <;> simp_all [uiNearVertices, uiFar2Vertices, uiFar2, familyAdj] <;> omega
  · intro x hx hf
    cases x <;> simp_all [uiFar1Vertices, uiFar2Vertices, uiFar1, uiFar2]
  · intro x hx; exact of_decide_eq_true (List.mem_filter.mp hx).2
  · intro x hx
    cases x <;> simp_all [uiFar1Vertices, uiFar1, familyAdj]
  · intro x hx
    cases x <;> simp_all [uiFar2Vertices, uiFar2, familyAdj]
  · exact ui_partition i hi

/-- The endpoints of a matching edge have disjoint open neighborhoods. -/
theorem matched_no_common {m n : Nat} (j : Fin (m + n)) (z : Vertex m n) :
    ¬ (familyAdj (.u j) z ∧ familyAdj (.v j) z) := by
  intro h
  cases z with
  | w => exact h.2
  | u k => exact h.1.1 h.2
  | v k => exact h.2 h.1

theorem other_independent_index {m n : Nat} (hn : 2 ≤ n) (i : Fin (m + n)) :
    ∃ j : Fin (m + n), m ≤ j.val ∧ j ≠ i := by
  by_cases him : i.val = m
  · refine ⟨⟨m + 1, by omega⟩, by simp, ?_⟩
    intro h; have := congrArg Fin.val h; simp at this; omega
  · refine ⟨⟨m, by omega⟩, by simp, ?_⟩
    intro h; have := congrArg Fin.val h; simp at this; omega

/-- Proposition 3.2(c), including all m>=0 and n>=2. -/
theorem target_ui {m n : Nat} (hn : 2 ≤ n) (i : Fin (m + n))
    (hi : m ≤ i.val) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (.u i) t (4 * t + 1) := by
  obtain ⟨j, hj, hji⟩ := other_independent_index hn i
  have hilt : ¬ i.val < m := by omega
  have hjlt : ¬ j.val < m := by omega
  apply target_number_of_bounds (ui_upper i hi t)
  refine ⟨(fun x => pile (.v j) (4 * t - 1) x + pile (.u j) 1 x), ?_, ?_⟩
  · rw [← sumOn_vertices, sumOn_add,
      sumOn_pile _ (vertices_nodup m n) _ (mem_vertices _) _,
      sumOn_pile _ (vertices_nodup m n) _ (mem_vertices _) _]
    omega
  · apply frozen_pair_obstruction (vertices m n) (vertices_nodup m n) mem_vertices
      familyAdj_irreflexive (.u i) (.u j) (.v j)
    · simp [levelWeight, familyAdj, hji, hilt, hjlt]
    · simp [levelWeight, familyAdj, hji]
    · simp
    · intro z _; exact matched_no_common j z
    · exact ht

end RubblingFamily

#print axioms RubblingFamily.ui_upper
#print axioms RubblingFamily.target_ui

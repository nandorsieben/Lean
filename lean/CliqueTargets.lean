import CommonNeighbor

namespace RubblingFamily

theorem uc_common {m n : Nat} (i : Fin (m + n)) (hi : i.val < m)
    (x : Vertex m n) (_hx : x ≠ .u i) (hfar : ¬ familyAdj x (.u i)) :
    familyAdj x (.v i) := by
  cases x with
  | w => simp [familyAdj] at hfar
  | u j => simpa [familyAdj, hi] using hfar
  | v j => simpa [familyAdj] using hfar

theorem vc_common {m n : Nat} (i : Fin (m + n)) (hi : i.val < m)
    (x : Vertex m n) (_hx : x ≠ .v i) (hfar : ¬ familyAdj x (.v i)) :
    familyAdj x (.u i) := by
  cases x with
  | w => trivial
  | u j => simpa [familyAdj, hi] using hfar
  | v j => simpa [familyAdj] using hfar

/-- Proposition 3.2(b): every U_C target, for all family parameters and t. -/
theorem target_uc {m n : Nat} (hn : 1 ≤ n) (i : Fin (m + n))
    (hi : i.val < m) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (.u i) t (4 * t) := by
  let j : Fin (m + n) := ⟨m, by omega⟩
  have hji : j ≠ i := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
  have h := common_neighbor_target (vertices m n) (vertices_nodup m n) mem_vertices
    familyAdj_irreflexive (.u i) (.v i) (by simp [familyAdj]) (uc_common i hi)
    (.v j) (by simp) (by simpa [familyAdj] using hji) t ht
  simpa only [TargetNumberIs, TargetUpperBound, sumOn_vertices] using h

/-- Proposition 3.2(b): every V_C target. -/
theorem target_vc {m n : Nat} (i : Fin (m + n))
    (hi : i.val < m) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (.v i) t (4 * t) := by
  have h := common_neighbor_target (vertices m n) (vertices_nodup m n) mem_vertices
    familyAdj_irreflexive (.v i) (.u i) (by simp [familyAdj]) (vc_common i hi)
    .w (by simp) (by simp [familyAdj]) t ht
  simpa only [TargetNumberIs, TargetUpperBound, sumOn_vertices] using h

def lastIndex (m : Nat) : Fin (m + 1) := ⟨m, by omega⟩

theorem index_before_last {m : Nat} (j : Fin (m + 1)) (hj : j ≠ lastIndex m) :
    j.val < m := by
  have hval : j.val ≠ m := by
    intro h; apply hj; apply Fin.ext; exact h
  have := j.isLt
  omega

theorem ui_one_common (m : Nat) (x : Vertex m 1)
    (_hx : x ≠ .u (lastIndex m)) (hfar : ¬ familyAdj x (.u (lastIndex m))) :
    familyAdj x (.v (lastIndex m)) := by
  cases x with
  | w => simp [familyAdj] at hfar
  | u j =>
    by_cases hji : j = lastIndex m
    · simp [familyAdj, hji]
    · have hj := index_before_last j hji
      simp [familyAdj, hji, hj] at hfar
  | v j => simpa [familyAdj] using hfar

theorem vi_one_common (m : Nat) (x : Vertex m 1)
    (_hx : x ≠ .v (lastIndex m)) (hfar : ¬ familyAdj x (.v (lastIndex m))) :
    familyAdj x (.u (lastIndex m)) := by
  cases x with
  | w => trivial
  | u j =>
    have hji : j ≠ lastIndex m := by simpa [familyAdj] using hfar
    have hj := index_before_last j hji
    simp [familyAdj, hji, hj]
  | v j => simpa [familyAdj] using hfar

/-- The n=1 U_I boundary, excluding the middle vertex of P_3. -/
theorem target_ui_one (m : Nat) (hm : 1 ≤ m) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (.u (lastIndex m)) t (4 * t) := by
  let j : Fin (m + 1) := ⟨0, by omega⟩
  have hji : j ≠ lastIndex m := by
    intro h; have := congrArg Fin.val h; dsimp [j, lastIndex] at this; omega
  have h := common_neighbor_target (vertices m 1) (vertices_nodup m 1) mem_vertices
    familyAdj_irreflexive (.u (lastIndex m)) (.v (lastIndex m))
    (by simp [familyAdj]) (ui_one_common m) (.v j) (by simp)
    (by simpa [familyAdj] using hji) t ht
  simpa only [TargetNumberIs, TargetUpperBound, sumOn_vertices] using h

/-- The n=1 V_I boundary, including the right endpoint of P_3. -/
theorem target_vi_one (m : Nat) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (.v (lastIndex m)) t (4 * t) := by
  have h := common_neighbor_target (vertices m 1) (vertices_nodup m 1) mem_vertices
    familyAdj_irreflexive (.v (lastIndex m)) (.u (lastIndex m))
    (by simp [familyAdj]) (vi_one_common m) .w (by simp) (by simp [familyAdj]) t ht
  simpa only [TargetNumberIs, TargetUpperBound, sumOn_vertices] using h

end RubblingFamily

#print axioms RubblingFamily.target_uc
#print axioms RubblingFamily.target_vc
#print axioms RubblingFamily.target_ui_one
#print axioms RubblingFamily.target_vi_one

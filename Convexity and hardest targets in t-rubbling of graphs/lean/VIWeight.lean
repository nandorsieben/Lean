import ParityWeight
import CommonNeighbor

namespace RubblingFamily
open VICategory

/-- The paper's far sets: far1 is U_I without the matched u_i; far2 is {w} union U_C. -/
def viCategory {m n : Nat} (i : Fin (m+n)) : Vertex m n → VICategory
  | .w => far2
  | .u j => if j=i then near else if j.val<m then far2 else far1
  | .v j => if j=i then root else near

theorem conditional_eq {β : Type} (P : Prop) [Decidable P] (a b c : β) :
    (if P then a else b)=c ↔ (P ∧ a=c) ∨ (¬P ∧ b=c) := by
  by_cases h : P <;> simp [h]

set_option maxHeartbeats 1000000 in
theorem vi_allowed_pair {m n : Nat} (i : Fin (m+n)) (_hi : m≤i.val)
    (u z : Vertex m n) (h : familyAdj u z) :
    viAllowed true (viCategory i u) (viCategory i u) (viCategory i z) := by
  generalize huC : viCategory i u = cu
  generalize hzC : viCategory i z = cz
  cases cu <;> cases cz <;> simp_all [viAllowed]
  all_goals cases u <;> cases z <;> simp_all [familyAdj,viCategory,conditional_eq] <;> omega

set_option maxHeartbeats 1000000 in
theorem vi_allowed_strict {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val)
    (u v z : Vertex m n) (hu : familyAdj u z) (hv : familyAdj v z) (hne : u≠v) :
    viAllowed false (viCategory i u) (viCategory i v) (viCategory i z) := by
  generalize huC : viCategory i u = cu
  generalize hvC : viCategory i v = cv
  generalize hzC : viCategory i z = cz
  cases cu <;> cases cv <;> cases cz <;> simp_all [viAllowed]
  all_goals cases u <;> cases v <;> cases z <;> simp_all [familyAdj,viCategory,conditional_eq] <;> omega

def viWeight {m n : Nat} (i : Fin (m+n)) (p : Distribution (Vertex m n)) :=
  sumOn (vertices m n) (fun x => viPhi (viCategory i x) (p x)) +
  sumOn (vertices m n) (fun x => viPsi (viCategory i x) (p x))/2

theorem viWeight_move {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val)
    {p q : Distribution (Vertex m n)} (hm : LegalMove familyAdj p q) :
    viWeight i q ≤ viWeight i p := by
  apply parity_weight_move (vertices m n) (vertices_nodup _ _) mem_vertices
    familyAdj_irreflexive (fun x => viPhi (viCategory i x))
      (fun x => viPsi (viCategory i x)) (hm := hm)
  · intro u z a a' b b' A A' O O' hu ha hb hA hO
    exact vi_pair_numeric _ _ _ _ _ _ _ _ _ _ (vi_allowed_pair i hi u z hu) ha hb hA hO
  · intro u v z a a' b b' c c' A A' O O' hu hv hne ha hb hc hA hO
    exact vi_strict_numeric _ _ _ _ _ _ _ _ _ _ _ _ _
      (vi_allowed_strict i hi u v z hu hv hne) ha hb hc hA hO

theorem viWeight_root {m n : Nat} (i : Fin (m+n))
    (p : Distribution (Vertex m n)) : 4*p (.v i) ≤ viWeight i p := by
  have h := member_le_sumOn (vertices m n)
    (fun x => viPhi (viCategory i x) (p x)) (.v i) (mem_vertices _)
  simp only [viCategory, ↓reduceIte, viPhi] at h
  change 4*p (.v i) ≤
    sumOn (vertices m n) (fun x => viPhi (viCategory i x) (p x)) + _
  exact Nat.le_trans h (Nat.le_add_right _ _)

end RubblingFamily
#print axioms RubblingFamily.viWeight_move

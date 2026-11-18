import VIWeight
import WLower

namespace RubblingFamily

def skipIndex {m n : Nat} (i : Fin (m+n)) (_hi : m≤i.val)
    (o : Nat) (ho : o≤n-1) (j : Fin o) : Fin (m+n) :=
  ⟨if m+j.val<i.val then m+j.val else m+j.val+1, by split <;> omega⟩

theorem skipIndex_props {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val)
    (o : Nat) (ho : o≤n-1) (j : Fin o) :
    m≤(skipIndex i hi o ho j).val ∧ skipIndex i hi o ho j ≠ i := by
  unfold skipIndex
  constructor
  · split <;> dsimp only <;> omega
  · intro h
    have hh := congrArg Fin.val h
    dsimp only at hh
    split at hh <;> omega

theorem skipIndex_injective {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val)
    (o : Nat) (ho : o≤n-1) (a b : Fin o)
    (h : skipIndex i hi o ho a=skipIndex i hi o ho b) : a=b := by
  have hh := congrArg Fin.val h
  simp only [skipIndex] at hh
  apply Fin.ext
  split at hh <;> split at hh <;> omega

/-- The parity weight certifies the general V_I lower-bound distribution. -/
theorem vi_lower {m n : Nat} (hn : 2≤n) (i : Fin (m+n)) (hi : m≤i.val)
    (t : Nat) (ht : 1≤t) :
    ∃ p : Distribution (Vertex m n),
      familySize p+1=4*t+min (4*t) (n/2) ∧
      ¬TReachable familyAdj p (.v i) t := by
  let f := min (4*t) (n/2)
  let o := 2*f-1
  have hp := vi_lower_parameters n t hn ht
  change 1≤o ∧ o≤n-1 ∧ _ at hp
  obtain ⟨_, ho, hsize, hweight⟩ := hp
  let M : List (Vertex m n) := List.ofFn (fun j : Fin o => .u (skipIndex i hi o ho j))
  have hM : M.Nodup := nodup_ofFn _ (by
    intro a b hab
    exact skipIndex_injective i hi o ho a b (Vertex.u.inj hab))
  have hlen : M.length=o := by simp [M]
  have hwM : (Vertex.w : Vertex m n) ∉ M := by simp [M,List.mem_ofFn]
  have hcat : ∀ x ∈ M, viCategory i x = VICategory.far1 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨hj, hji⟩ := skipIndex_props i hi o ho j
    simp [viCategory,hji,Nat.not_lt.mpr hj]
  let p : Distribution (Vertex m n) :=
    fun x => pile .w (4*t-f) x + if x∈M then 1 else 0
  have hcount := sumOn_membership (vertices m n) M (vertices_nodup _ _) hM
    (by intro x _; exact mem_vertices x)
  have hnorm : familySize p=(4*t-f)+o := by
    rw [←sumOn_vertices]
    change sumOn (vertices m n) (fun x => pile .w (4*t-f) x + (if x∈M then 1 else 0)) = _
    rw [sumOn_add,sumOn_pile _ (vertices_nodup _ _) .w (mem_vertices _) (4*t-f),hcount,hlen]
  have hphi : ∀ x ∈ vertices m n, viPhi (viCategory i x) (p x) =
      if x=.w then 4*t-f else 0 := by
    intro x _
    by_cases hx : x=.w
    · subst x; simp [p,pile,hwM,viCategory,viPhi]
    · by_cases hxM : x∈M
      · rw [hcat x hxM]; simp [p,pile,hx,hxM,viPhi]
      · simp only [p,pile,hx,hxM,↓reduceIte,Nat.zero_add]
        cases viCategory i x <;> rfl
  have hpsi : ∀ x ∈ vertices m n, viPsi (viCategory i x) (p x) =
      if x∈M then 1 else 0 := by
    intro x _
    by_cases hx : x=.w
    · subst x; simp [p,pile,hwM,viCategory,viPsi]
    · by_cases hxM : x∈M
      · rw [hcat x hxM]; simp [p,pile,hx,hxM,viPsi]
      · simp only [p,pile,hx,hxM,↓reduceIte,Nat.zero_add]
        cases viCategory i x <;> rfl
  have hw : viWeight i p=(4*t-f)+o/2 := by
    unfold viWeight
    rw [sumOn_congr _ _ _ hphi,sumOn_congr _ _ _ hpsi,
      sumOn_indicator _ (vertices_nodup _ _) .w,hcount,hlen]
    simp [mem_vertices]
  refine ⟨p,by omega,?_⟩
  apply not_t_reachable_of_weight (viWeight_move i hi) (viWeight_root i)
  rw [hw]
  omega

end RubblingFamily
#print axioms RubblingFamily.vi_lower

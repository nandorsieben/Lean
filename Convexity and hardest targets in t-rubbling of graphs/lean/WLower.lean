import Separable
import CommonNeighbor
import Arithmetic

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

/-- Counting the indicator of a sublist, without choosing a finite-set library. -/
theorem sumOn_membership (L M : List α) (hL : L.Nodup) (hM : M.Nodup)
    (hsub : ∀ x ∈ M, x ∈ L) :
    sumOn L (fun x => if x ∈ M then 1 else 0) = M.length := by
  induction M with
  | nil => simp [sumOn_zero]
  | cons a M ih =>
    have ha := (List.nodup_cons.mp hM).1
    have ht := (List.nodup_cons.mp hM).2
    have heq : ∀ x ∈ L, (if x ∈ a :: M then 1 else 0) =
        (if x = a then 1 else 0) + (if x ∈ M then 1 else 0) := by
      intro x _
      by_cases hx : x = a
      · subst x; simp [ha]
      · simp [hx]
    rw [sumOn_congr L _ _ heq, sumOn_add, sumOn_indicator L hL]
    have hac := hsub a (by simp)
    have htail := ih ht (by intro x hx; exact hsub x (by simp [hx]))
    simp [hac, htail, Nat.add_comm]

def firstV (m n o : Nat) (ho : o ≤ m + n) : List (Vertex m n) :=
  List.ofFn (fun j : Fin o => Vertex.v ⟨j.val, by omega⟩)

theorem firstV_nodup (m n o : Nat) (ho : o ≤ m + n) :
    (firstV m n o ho).Nodup := by
  apply nodup_ofFn
  intro i j h
  have hv : i.val = j.val := congrArg (fun x : Fin (m+n) => x.val) (Vertex.v.inj h)
  exact Fin.ext hv

theorem w_lower {m n : Nat} (hk : 2 ≤ m + n) (t : Nat) (ht : 1 ≤ t) :
    ∃ p : Distribution (Vertex m n),
      familySize p + 1 = 4 * t + min (2 * t) ((m + n + 1) / 3) ∧
      ¬ TReachable familyAdj p .w t := by
  let f := min (2 * t) ((m + n + 1) / 3)
  let o := 3 * f - 1
  have hf : f ≤ 2 * t := Nat.min_le_left _ _
  have hp := w_lower_parameters (m + n) t hk ht
  change 2 ≤ o ∧ o ≤ m + n ∧ _ at hp
  obtain ⟨ho2, hok, hsize, hweight⟩ := hp
  let M := firstV m n o hok
  let v0 : Vertex m n := .v ⟨0, by omega⟩
  have hM : M.Nodup := firstV_nodup _ _ _ _
  have hlen : M.length = o := by simp [M, firstV]
  have hv0 : v0 ∈ M := by
    apply List.mem_ofFn.mpr
    exact ⟨⟨0, by omega⟩, rfl⟩
  let p : Distribution (Vertex m n) :=
    fun x => pile v0 (4 * t - 2 * f) x + if x ∈ M then 1 else 0
  have hcount := sumOn_membership (vertices m n) M (vertices_nodup _ _) hM
    (by intro x _; exact mem_vertices x)
  have hnorm : familySize p = (4 * t - 2 * f) + o := by
    rw [← sumOn_vertices]
    change sumOn (vertices m n) (fun x => pile v0 (4*t-2*f) x +
      (if x ∈ M then 1 else 0)) = _
    rw [sumOn_add, sumOn_pile _ (vertices_nodup _ _) v0 (mem_vertices _) , hcount, hlen]
  have hpoint : ∀ x ∈ vertices m n, wPhi x (p x) =
      (if x = v0 then 6 * t - 3 * f else 0) + (if x ∈ M then 1 else 0) := by
    intro x _
    by_cases hx : x = v0
    · subst x
      simp only [p, pile, ↓reduceIte, hv0, wPhi, v0]
      omega
    · by_cases hxm : x ∈ M
      · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hxm
        change Vertex.v _ = x at hj
        subst x
        simp only [p, pile, hx, hxm, ↓reduceIte, Nat.zero_add, wPhi]
      · cases x <;> simp [p, pile, hx, hxm, wPhi]
  have hw : wWeight p = (6*t-3*f) + o := by
    unfold wWeight
    rw [sumOn_congr _ _ _ hpoint, sumOn_add,
      sumOn_indicator _ (vertices_nodup _ _) v0, hcount, hlen]
    simp [mem_vertices]
  refine ⟨p, by omega, ?_⟩
  apply not_t_reachable_of_weight wWeight_move wWeight_root
  rw [hw]
  omega

end RubblingFamily

#print axioms RubblingFamily.w_lower

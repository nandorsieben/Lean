import VILower
import WTargets
import TwoFar

namespace RubblingFamily
open VICategory

def viClassVertices {m n : Nat} (i : Fin (m+n)) (c : VICategory) : List (Vertex m n) :=
  (vertices m n).filter (fun x => decide (viCategory i x=c))

theorem mem_viClass {m n : Nat} (i : Fin (m+n)) (c : VICategory) (x : Vertex m n) :
    x∈viClassVertices i c ↔ viCategory i x=c := by
  simp [viClassVertices,mem_vertices]

theorem skipIndex_surjective {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val)
    (j : Fin (m+n)) (hj : m≤j.val) (hji : j≠i) :
    ∃ a : Fin (n-1), skipIndex i hi (n-1) (Nat.le_refl _) a=j := by
  have hval : j.val≠i.val := by intro h; exact hji (Fin.ext h)
  by_cases hlt : j.val<i.val
  · refine ⟨⟨j.val-m,by omega⟩,?_⟩
    apply Fin.ext
    have hv : m+(j.val-m)=j.val := by omega
    simp [skipIndex,hv,hlt]
  · refine ⟨⟨j.val-m-1,by omega⟩,?_⟩
    apply Fin.ext
    have hv : m+(j.val-m-1)+1=j.val := by omega
    have hv' : ¬m+(j.val-m-1)<i.val := by omega
    simp [skipIndex,hv,hv']

theorem vi_far1_length {m n : Nat} (i : Fin (m+n)) (hi : m≤i.val) :
    (viClassVertices i far1).length=n-1 := by
  let M : List (Vertex m n) := List.ofFn
    (fun a : Fin (n-1) => .u (skipIndex i hi (n-1) (Nat.le_refl _) a))
  have hM : M.Nodup := nodup_ofFn _ (by
    intro a b h
    exact skipIndex_injective i hi _ _ a b (Vertex.u.inj h))
  have hmem : ∀ x, x∈viClassVertices i far1 ↔ x∈M := by
    intro x
    rw [mem_viClass]
    constructor
    · intro hx
      cases x with
      | w => cases hx
      | v j => simp [viCategory,conditional_eq] at hx
      | u j =>
        have hj : m≤j.val ∧ j≠i := by
          simpa [viCategory,conditional_eq,and_comm] using hx
        obtain ⟨a, ha⟩ := skipIndex_surjective i hi j hj.1 hj.2
        exact List.mem_ofFn.mpr ⟨a,congrArg Vertex.u ha⟩
    · intro hx
      obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨ha, hai⟩ := skipIndex_props i hi _ (Nat.le_refl _) a
      simp [viCategory,hai,Nat.not_lt.mpr ha]
  have hF : (viClassVertices i far1).Nodup :=
    List.Pairwise.filter _ (vertices_nodup _ _)
  have hp : (viClassVertices i far1).Perm M := List.perm_iff_count.mpr (by
    intro x
    rw [hF.count,hM.count]
    simp [hmem x])
  have hlen := hp.length_eq
  simpa [M] using hlen

theorem vi_partition {m n : Nat} (i : Fin (m+n))
    (p : Distribution (Vertex m n)) :
    familySize p=p (.v i)+sumOn (viClassVertices i near) p+
      sumOn (viClassVertices i far2) p+sumOn (viClassVertices i far1) p := by
  have hpoint : ∀ x∈vertices m n, p x=
      (if x=.v i then p (.v i) else 0)+
      (if viCategory i x=near then p x else 0)+
      (if viCategory i x=far2 then p x else 0)+
      (if viCategory i x=far1 then p x else 0) := by
    intro x _
    cases x with
    | w => simp [viCategory]
    | u j =>
      by_cases hji : j=i <;> by_cases hj : j.val<m <;> simp [viCategory,hji,hj]
    | v j => by_cases hji : j=i <;> simp [viCategory,hji]
  have h := sumOn_congr (vertices m n) _ _ hpoint
  rw [sumOn_add,sumOn_add,sumOn_add,sumOn_indicator _ (vertices_nodup _ _)] at h
  rw [←sumOn_vertices p]
  unfold viClassVertices
  rw [sumOn_bool_filter,sumOn_bool_filter,sumOn_bool_filter]
  simpa only [mem_vertices,↓reduceIte,decide_eq_true_eq] using h

/-- All deliveries used in case (d) are realized by legal rubbling sequences. -/
theorem vi_upper {m n : Nat} (hn : 1≤n) (i : Fin (m+n)) (hi : m≤i.val) (t : Nat) :
    TargetUpperBound familyAdj familySize (.v i) t (4*t+min (4*t) (n/2)) := by
  intro p hp
  let N := viClassVertices i near
  let F1 := viClassVertices i far1
  let F2 := viClassVertices i far2
  have hN : N.Nodup := List.Pairwise.filter _ (vertices_nodup _ _)
  have h2 : F2.Nodup := List.Pairwise.filter _ (vertices_nodup _ _)
  have h1 : F1.Nodup := List.Pairwise.filter _ (vertices_nodup _ _)
  have hN2 : ∀ x∈N, x∉F2 := by intro x hx hf; have := (mem_viClass i near x).mp hx; have := (mem_viClass i far2 x).mp hf; simp_all
  have hN1 : ∀ x∈N, x∉F1 := by intro x hx hf; have := (mem_viClass i near x).mp hx; have := (mem_viClass i far1 x).mp hf; simp_all
  have h21 : ∀ x∈F2, x∉F1 := by intro x hx hf; have := (mem_viClass i far2 x).mp hx; have := (mem_viClass i far1 x).mp hf; simp_all
  have hrN : Vertex.v i∉N := by simp [N,mem_viClass,viCategory]
  have hr2 : Vertex.v i∉F2 := by simp [F2,mem_viClass,viCategory]
  have hr1 : Vertex.v i∉F1 := by simp [F1,mem_viClass,viCategory]
  have hw2 : Vertex.w∈F2 := by simp [F2,mem_viClass,viCategory]
  have hwN : Vertex.w∉N := by simp [N,mem_viClass,viCategory]
  have hw1 : Vertex.w∉F1 := by simp [F1,mem_viClass,viCategory]
  have huN : Vertex.u i∈N := by simp [N,mem_viClass,viCategory]
  let sink : Vertex m n → Vertex m n | .u j => .v j | x => x
  have h1shape : ∀ x∈F1, ∃ j, x=Vertex.u j ∧ m≤j.val ∧ j≠i := by
    intro x hx
    have hcat := (mem_viClass i far1 x).mp hx
    cases x with
    | w => cases hcat
    | v j => simp [viCategory,conditional_eq] at hcat
    | u j =>
      refine ⟨j,rfl,?_⟩
      simpa [viCategory,conditional_eq,and_comm] using hcat
  have hsink : ∀ x∈F1, sink x∈N := by
    intro x hx
    obtain ⟨j,rfl,_,hji⟩ := h1shape x hx
    simp [N,mem_viClass,sink,viCategory,hji]
  have hadj : ∀ x∈F1, familyAdj x (sink x) := by
    intro x hx
    obtain ⟨j,rfl,_,_⟩ := h1shape x hx
    simp [sink,familyAdj]
  let a := p (.v i)
  let b := sumOn N p
  let d := sumOn F2 p
  let e := sumOn F1 (fun x => p x/2)
  let o := sumOn F1 (dot p)
  have ho : o≤n-1 := by
    have h := sumOn_le_length F1 (fun x => p x%2) (by intro x _; omega)
    rw [vi_far1_length i hi] at h
    exact h
  have hnorm : familySize p=a+b+d+2*e+o := by
    have h := vi_partition i p
    have he := sumOn_congr F1 p (fun x => 2*(p x/2)+p x%2)
      (by intro x _; omega)
    rw [sumOn_add,sumOn_twice] at he
    change familySize p=a+b+d+sumOn F1 p at h
    change familySize p = a+b+d+2*sumOn F1 (fun x => p x/2) +
      sumOn F1 (fun x => p x%2)
    omega
  obtain ⟨q,hpq,hq1,hqN,hqo⟩ := drain_pairs F1 N h1 hN
    (by intro x hx hxn; exact hN1 x hxn hx) sink hsink hadj p
  have hqmass : sumOn F1 q=o := sumOn_congr F1 q _ hq1
  have hq2 : sumOn F2 q=d := sumOn_congr F2 q p (by
    intro x hx
    exact hqo x (h21 x hx) (by intro h; exact hN2 x h hx))
  obtain ⟨s,hqs,hsw,_,hso⟩ := collect_pairs (adj := familyAdj) F1 h1 Vertex.w hw1
    (by intro x hx; obtain ⟨j,rfl,_,_⟩ := h1shape x hx; trivial) q
  have hs2 : sumOn F2 s=d+o/2 := by
    have h := sumOn_single_change F2 F1 h2 Vertex.w hw2 h21 q s _ hsw hso
    rw [h,hq2,hqmass]
  have hsN : sumOn N s=b+e := by
    have h := sumOn_congr N s q (by intro x hx; exact hso x (hN1 x hx) (by intro heq; exact hwN (heq ▸ hx)))
    rw [h,hqN]
  obtain ⟨v,hsv,hvu,_,hvo⟩ := collect_pairs (adj := familyAdj) F2 h2 (Vertex.u i)
    (hN2 _ huN) (by
      intro x hx
      have hcat := (mem_viClass i far2 x).mp hx
      cases x with
      | w => trivial
      | v j => simp [viCategory,conditional_eq] at hcat
      | u j =>
        have hj : j≠i ∧ j.val<m := by simpa [viCategory,conditional_eq,and_comm] using hcat
        exact ⟨hj.1,Or.inl hj.2⟩) s
  have hvN : sumOn N v=b+e+(d+o/2)/2 := by
    have h := sumOn_single_change N F2 hN (Vertex.u i) huN hN2 s v _ hvu hvo
    rw [h,hsN,hs2]
  have hvr : v (.v i)=a := by
    rw [hvo _ hr2 (by intro h; cases h),hso _ hr1 (by intro h; cases h),hqo _ hr1 hrN]
  obtain ⟨z,hvz,hzr,_,_⟩ := collect_pairs (adj := familyAdj) N hN (Vertex.v i) hrN
    (by
      intro x hx
      have hcat := (mem_viClass i near x).mp hx
      cases x with
      | w => cases hcat
      | u j =>
        have hj : j=i := by simpa [viCategory,conditional_eq,and_comm] using hcat
        exact hj
      | v j =>
        have hj : j≠i := by simpa [viCategory,conditional_eq,and_comm] using hcat
        exact hj) v
  refine ⟨z,hpq.trans (hqs.trans (hsv.trans hvz)),?_⟩
  by_cases hgood : t≤z (.v i)
  · exact hgood
  · have hlose : a+(b+e+(d+o/2)/2)/2<t := by rw [hzr,hvr,hvN] at hgood; omega
    have h := vi_upper_arithmetic a b d e o n t hn ho hlose
    omega

theorem target_vi {m n : Nat} (hn : 2≤n) (i : Fin (m+n)) (hi : m≤i.val)
    (t : Nat) (ht : 1≤t) :
    TargetNumberIs familyAdj familySize (.v i) t (4*t+min (4*t) (n/2)) :=
  target_number_of_bounds (vi_upper (by omega) i hi t) (vi_lower hn i hi t ht)

end RubblingFamily
#print axioms RubblingFamily.target_vi

import WLower
import Drain
import Triples

namespace RubblingFamily

def uVertices (m n : Nat) : List (Vertex m n) := List.ofFn Vertex.u
def vVertices (m n : Nat) : List (Vertex m n) := List.ofFn Vertex.v

theorem sumOn_le_length {α : Type} (L : List α) (p : α → Nat)
    (h : ∀ x ∈ L, p x ≤ 1) : sumOn L p ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [sumOn_cons, List.length_cons]
    omega

theorem sumOn_twice {α : Type} (L : List α) (p : α → Nat) :
    sumOn L (fun x => 2 * p x) = 2 * sumOn L p := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [sumOn_cons, ih]; omega

theorem w_upper {m n : Nat} (t : Nat) :
    TargetUpperBound familyAdj familySize (Vertex.w : Vertex m n) t
      (4 * t + min (2 * t) ((m+n+1)/3)) := by
  intro p hsize
  let U := uVertices m n
  let V := vVertices m n
  let sink : Vertex m n → Vertex m n
    | .v i => .u i
    | x => x
  have hU : U.Nodup := nodup_ofFn _ (by intro i j h; exact Vertex.u.inj h)
  have hV : V.Nodup := nodup_ofFn _ (by intro i j h; exact Vertex.v.inj h)
  have hdis : ∀ x ∈ V, x ∉ U := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp [U, uVertices, List.mem_ofFn]
  have hsink : ∀ x ∈ V, sink x ∈ U := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp [sink, U, uVertices, List.mem_ofFn]
  have hadj : ∀ x ∈ V, familyAdj x (sink x) := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp [sink, familyAdj]
  have hwU : (Vertex.w : Vertex m n) ∉ U := by simp [U, uVertices, List.mem_ofFn]
  have hwV : (Vertex.w : Vertex m n) ∉ V := by simp [V, vVertices, List.mem_ofFn]
  let a := p .w
  let b := sumOn U p
  let e := sumOn V (fun x => p x / 2)
  let o := sumOn V (dot p)
  have ho : o ≤ m+n := by
    change sumOn V (fun x => p x % 2) ≤ m+n
    have h := sumOn_le_length V (fun x => p x % 2) (by intro x _; omega)
    simpa [V, vVertices] using h
  have hnorm : familySize p = a+b+2*e+o := by
    have hh := sumOn_congr V p (fun x => 2*(p x/2)+p x%2) (by intro x _; omega)
    rw [sumOn_add, sumOn_twice] at hh
    have hsize' : familySize p = a+b+sumOn V p := by
      simp [familySize, a, b, U, V, uVertices, vVertices, sumOn, List.map_ofFn,
        Function.comp_def]
    rw [hsize', hh]
    simp only [e, o, Nat.add_assoc]
  obtain ⟨q, hpq, hqV, hqU, hqo⟩ := drain_pairs V U hV hU hdis sink hsink hadj p
  have hqmass : sumOn V q = o := sumOn_congr V q _ hqV
  have hqsingle : ∀ x ∈ V, q x ≤ 1 := by intro x hx; rw [hqV x hx]; omega
  have hclique : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → familyAdj x y := by
    intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact fun h => hxy (congrArg Vertex.v h)
  obtain ⟨s, hqs, _, _, hsU, hso⟩ :=
    collect_triples V U hV hU hdis sink hsink hadj hclique q hqsingle
  obtain ⟨z, hsz, hzw, _, _⟩ := collect_pairs (adj := familyAdj) U hU (Vertex.w : Vertex m n) hwU
    (by intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; trivial) s
  have hsw : s .w = a := by rw [hso .w hwV hwU, hqo .w hwV hwU]
  have hdeliver : z .w = a+(b+e+o/3)/2 := by
    rw [hzw, hsw, hsU, hqU, hqmass]
  refine ⟨z, hpq.trans (hqs.trans hsz), ?_⟩
  by_cases hgood : t ≤ z .w
  · exact hgood
  · have hlt : a+(b+e+o/3)/2 < t := by omega
    have h := w_upper_arithmetic a b e o (m+n) t ho hlt
    omega

theorem target_w {m n : Nat} (hk : 2 ≤ m+n) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs familyAdj familySize (Vertex.w : Vertex m n) t
      (4*t + min (2*t) ((m+n+1)/3)) :=
  target_number_of_bounds (w_upper t) (w_lower hk t ht)

end RubblingFamily
#print axioms RubblingFamily.target_w

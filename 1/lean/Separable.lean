import Finite

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

theorem sumOn_local_two (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    (a b : α) (hab : a ≠ b) (p q : α → Nat)
    (hother : ∀ x, x ≠ a → x ≠ b → q x = p x) :
    sumOn L q + p a + p b = sumOn L p + q a + q b := by
  have hpoint : ∀ x ∈ L,
      q x + (if x = a then p a else 0) + (if x = b then p b else 0) =
      p x + (if x = a then q a else 0) + (if x = b then q b else 0) := by
    intro x _
    by_cases ha : x = a
    · subst x; simp only [hab, ↓reduceIte, Nat.add_zero]; omega
    · by_cases hb : x = b
      · subst x; simp only [Ne.symm hab, ↓reduceIte, Nat.add_zero]; omega
      · simp [ha, hb, hother x ha hb]
  have h := sumOn_congr L _ _ hpoint
  simpa only [sumOn_add, sumOn_indicator L hn, hcover, ↓reduceIte] using h

theorem sumOn_local_three (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p q : α → Nat)
    (hother : ∀ x, x ≠ a → x ≠ b → x ≠ c → q x = p x) :
    sumOn L q + p a + p b + p c = sumOn L p + q a + q b + q c := by
  have hpoint : ∀ x ∈ L,
      q x + (if x = a then p a else 0) + (if x = b then p b else 0) +
        (if x = c then p c else 0) =
      p x + (if x = a then q a else 0) + (if x = b then q b else 0) +
        (if x = c then q c else 0) := by
    intro x _
    by_cases ha : x = a
    · subst x; simp only [hab, hac, ↓reduceIte, Nat.add_zero]; omega
    · by_cases hb : x = b
      · subst x; simp only [Ne.symm hab, hbc, ↓reduceIte, Nat.add_zero]; omega
      · by_cases hc : x = c
        · subst x; simp only [Ne.symm hac, Ne.symm hbc, ↓reduceIte, Nat.add_zero]; omega
        · simp [ha, hb, hc, hother x ha hb hc]
  have h := sumOn_congr L _ _ hpoint
  simpa only [sumOn_add, sumOn_indicator L hn, hcover, ↓reduceIte] using h

/-- Local two/three-vertex inequalities certify a separable global weight. -/
theorem separable_move (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} (hloop : ∀ x, ¬ adj x x) (φ : α → Nat → Nat)
    (hpair : ∀ u z a a' b b', adj u z → a' + 2 = a → b' = b + 1 →
      φ u a' + φ z b' ≤ φ u a + φ z b)
    (hstrict : ∀ u v z a a' b b' c c', adj u z → adj v z → u ≠ v →
      a' + 1 = a → b' + 1 = b → c' = c + 1 →
      φ u a' + φ v b' + φ z c' ≤ φ u a + φ v b + φ z c)
    {p q : Distribution α} (hm : LegalMove adj p q) :
    sumOn L (fun x => φ x (q x)) ≤ sumOn L (fun x => φ x (p x)) := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := hm
  have huz : u ≠ z := by intro h; subst u; exact hloop z hu
  have hvz : v ≠ z := by intro h; subst v; exact hloop z hv
  by_cases huv : u = v
  · subst v
    have hbu := hb u
    have hbz := hb z
    simp only [huz, Ne.symm huz, ↓reduceIte, Nat.add_zero] at hbu hbz
    have hlocal := hpair u z (p u) (q u) (p z) (q z) hu (by omega) (by omega)
    have hglobal := sumOn_local_two L hn hcover u z huz
      (fun x => φ x (p x)) (fun x => φ x (q x))
      (by intro x hxu hxz
          have hx := hb x
          have heq : q x = p x := by simpa [hxu, hxz] using hx
          exact congrArg (φ x) heq)
    omega
  · have hbu := hb u
    have hbv := hb v
    have hbz := hb z
    simp only [huv, Ne.symm huv, huz, hvz, Ne.symm huz, Ne.symm hvz,
      ↓reduceIte, Nat.add_zero] at hbu hbv hbz
    have hlocal := hstrict u v z (p u) (q u) (p v) (q v) (p z) (q z)
      hu hv huv (by omega) (by omega) (by omega)
    have hglobal := sumOn_local_three L hn hcover u v z huv huz hvz
      (fun x => φ x (p x)) (fun x => φ x (q x))
      (by intro x hxu hxv hxz
          have hx := hb x
          have heq : q x = p x := by simpa [hxu, hxv, hxz] using hx
          exact congrArg (φ x) heq)
    omega

def wPhi {m n : Nat} : Vertex m n → Nat → Nat
  | .w, a => 6 * a
  | .u _, a => 3 * a
  | .v _, a => (3 * a) / 2

def wWeight {m n : Nat} (p : Distribution (Vertex m n)) :=
  sumOn (vertices m n) (fun x => wPhi x (p x))

/-- The first nonstandard weight is nonincreasing for every legal move. -/
theorem wWeight_move {m n : Nat} {p q : Distribution (Vertex m n)}
    (hm : LegalMove familyAdj p q) : wWeight q ≤ wWeight p := by
  apply separable_move (vertices m n) (vertices_nodup m n) mem_vertices
    familyAdj_irreflexive wPhi (p := p) (q := q) (hm := hm)
  · intro u z a a' b b' hadj ha hb
    cases u <;> cases z <;> simp_all [familyAdj, wPhi] <;> omega
  · intro u v z a a' b b' c c' hu hv hne ha hb hc
    cases u <;> cases v <;> cases z <;> simp_all [familyAdj, wPhi] <;> omega

theorem wWeight_root {m n : Nat} (p : Distribution (Vertex m n)) :
    6 * p .w ≤ wWeight p := by
  have h := member_le_sumOn (vertices m n) (fun x => wPhi x (p x)) .w (mem_vertices _)
  exact h

end RubblingFamily

#print axioms RubblingFamily.wWeight_move

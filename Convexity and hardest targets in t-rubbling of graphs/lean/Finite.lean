import Routing

namespace RubblingFamily

variable {α : Type}

def sumOn (L : List α) (p : α → Nat) : Nat := (L.map p).sum

@[simp] theorem sumOn_nil (p : α → Nat) : sumOn [] p = 0 := rfl
@[simp] theorem sumOn_cons (x : α) (L : List α) (p : α → Nat) :
    sumOn (x :: L) p = p x + sumOn L p := rfl

@[simp] theorem sumOn_append (L M : List α) (p : α → Nat) :
    sumOn (L ++ M) p = sumOn L p + sumOn M p := by simp [sumOn]

theorem sumOn_congr (L : List α) (p q : α → Nat)
    (h : ∀ x ∈ L, p x = q x) : sumOn L p = sumOn L q := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [sumOn_cons, sumOn_cons, h x (by simp)]
    rw [ih (by intro y hy; exact h y (by simp [hy]))]

theorem sumOn_add (L : List α) (p q : α → Nat) :
    sumOn L (fun x => p x + q x) = sumOn L p + sumOn L q := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [sumOn_cons, ih]; omega

theorem sumOn_zero (L : List α) : sumOn L (fun _ => 0) = 0 := by
  induction L <;> simp_all

variable [DecidableEq α]

theorem sumOn_indicator (L : List α) (hn : L.Nodup) (u : α) (a : Nat) :
    sumOn L (fun x => if x = u then a else 0) = if u ∈ L then a else 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := List.nodup_cons.mp hn
    by_cases hu : x = u
    · subst x; simp [ih hL, hx]
    · simp [ih hL, hu, Ne.symm hu]

omit [DecidableEq α] in
theorem member_le_sumOn (L : List α) (p : α → Nat) (x : α) (hx : x ∈ L) :
    p x ≤ sumOn L p := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    simp only [List.mem_cons] at hx
    cases hx with
    | inl h => subst a; simp only [sumOn_cons]; omega
    | inr h => have := ih h; simp only [sumOn_cons]; omega

omit [DecidableEq α] in
theorem sumOn_pos (L : List α) (p : α → Nat) (h : 0 < sumOn L p) :
    ∃ x ∈ L, 0 < p x := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    by_cases ha : 0 < p a
    · exact ⟨a, by simp, ha⟩
    · have htail : 0 < sumOn L p := by rw [sumOn_cons] at h; omega
      obtain ⟨x, hx, hp⟩ := ih htail
      exact ⟨x, by simp [hx], hp⟩

/-- Sum the balance equations over an arbitrary duplicate-free vertex list. -/
theorem sumOn_balance (L : List α) (hn : L.Nodup) {p q : α → Nat} {u v z : α}
    (hb : ∀ x, q x + (if x = u then 1 else 0) + (if x = v then 1 else 0) =
      p x + (if x = z then 1 else 0)) :
    sumOn L q + (if u ∈ L then 1 else 0) + (if v ∈ L then 1 else 0) =
      sumOn L p + (if z ∈ L then 1 else 0) := by
  have h := sumOn_congr L _ _ (fun x _ => hb x)
  simpa only [sumOn_add, sumOn_indicator L hn] using h

/-- The corresponding balance equation for any nonnegative vertex weights. -/
theorem sumOn_weighted_balance (L : List α) (hn : L.Nodup) (w : α → Nat)
    {p q : α → Nat} {u v z : α}
    (hb : ∀ x, q x + (if x = u then 1 else 0) + (if x = v then 1 else 0) =
      p x + (if x = z then 1 else 0)) :
    sumOn L (fun x => w x * q x) + (if u ∈ L then w u else 0) +
      (if v ∈ L then w v else 0) =
    sumOn L (fun x => w x * p x) + (if z ∈ L then w z else 0) := by
  have hb' : ∀ x,
      w x * q x + (if x = u then w u else 0) + (if x = v then w v else 0) =
      w x * p x + (if x = z then w z else 0) := by
    intro x
    have h := congrArg (fun a => w x * a) (hb x)
    have hterm (y : α) :
        w x * (if x = y then 1 else 0) = if x = y then w y else 0 := by
      by_cases hxy : x = y <;> simp [hxy]
    simpa only [Nat.mul_add, hterm] using h

  have h := sumOn_congr L _ _ (fun x _ => hb' x)
  simpa only [sumOn_add, sumOn_indicator L hn] using h

omit [DecidableEq α] in
theorem nodup_ofFn {k : Nat} (f : Fin k → α)
    (hinj : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction k with
  | zero => simp [List.ofFn_zero]
  | succ k ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    refine ⟨?_, ih _ ?_⟩
    · intro h
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      have heq := hinj i.succ 0 hi
      have := congrArg Fin.val heq
      simp at this
    · intro i j hij
      have h := hinj i.succ j.succ hij
      exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

def vertices (m n : Nat) : List (Vertex m n) :=
  .w :: ((List.ofFn fun i => Vertex.u i) ++ (List.ofFn fun i => Vertex.v i))

theorem mem_vertices {m n : Nat} (x : Vertex m n) : x ∈ vertices m n := by
  cases x with
  | w => simp [vertices]
  | u i => simp [vertices, List.mem_ofFn]
  | v i => simp [vertices, List.mem_ofFn]

theorem vertices_nodup (m n : Nat) : (vertices m n).Nodup := by
  rw [vertices, List.nodup_cons, List.nodup_append]
  refine ⟨?_, nodup_ofFn _ (by intro i j h; cases h; rfl),
    nodup_ofFn _ (by intro i j h; cases h; rfl), ?_⟩
  · simp [List.mem_ofFn]
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    cases hxy

theorem sumOn_vertices {m n : Nat} (p : Distribution (Vertex m n)) :
    sumOn (vertices m n) p = familySize p := by
  simp [vertices, sumOn, List.map_ofFn, familySize, Nat.add_assoc, Function.comp_def]

omit [DecidableEq α] in
theorem sumOn_mono (L : List α) (p q : α → Nat)
    (h : ∀ x ∈ L, p x ≤ q x) : sumOn L p ≤ sumOn L q := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [sumOn_cons]
    omega

theorem sumOn_two_bound (L : List α) (hn : L.Nodup) (p : α → Nat)
    (r s : α) (hr : r ∈ L) (hs : s ∈ L) (hrs : r ≠ s) :
    p r + p s ≤ sumOn L p := by
  have h := sumOn_mono L
    (fun x => (if x = r then p r else 0) + (if x = s then p s else 0)) p
    (by intro x _
        by_cases hxr : x = r
        · subst x; simp [hrs]
        · by_cases hxs : x = s
          · subst x; simp [Ne.symm hrs]
          · simp [hxr, hxs])
  simpa only [sumOn_add, sumOn_indicator L hn, hr, hs, ↓reduceIte] using h

/-- Transfer into c changes the mass of a disjoint list containing c by exactly k. -/
theorem sumOn_single_change (M S : List α) (hM : M.Nodup) (c : α)
    (hc : c ∈ M) (hdisjoint : ∀ x ∈ M, x ∉ S)
    (p q : Distribution α) (k : Nat) (hqc : q c = p c + k)
    (hother : ∀ x, x ∉ S → x ≠ c → q x = p x) :
    sumOn M q = sumOn M p + k := by
  have hp : ∀ x ∈ M, q x = p x + (if x = c then k else 0) := by
    intro x hx
    by_cases hxc : x = c
    · subst x; simpa using hqc
    · simp [hxc, hother x (hdisjoint x hx) hxc]
  rw [sumOn_congr M _ _ hp, sumOn_add, sumOn_indicator M hM]
  simp [hc]

end RubblingFamily

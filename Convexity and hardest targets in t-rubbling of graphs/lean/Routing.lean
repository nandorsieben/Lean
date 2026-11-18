import Rubbling

namespace RubblingFamily

variable {α : Type} [DecidableEq α] {adj : α → α → Prop}

theorem Reachable.trans {p q r : Distribution α}
    (hpq : Reachable adj p q) (hqr : Reachable adj q r) : Reachable adj p r := by
  induction hqr with
  | refl => exact hpq
  | tail _ hm ih => exact Reachable.tail ih hm

/-- Execute one legal move explicitly, with no simultaneous-move assumption. -/
def fire (p : Distribution α) (u v z : α) : Distribution α := fun x =>
  p x - ((if x = u then 1 else 0) + (if x = v then 1 else 0)) +
    (if x = z then 1 else 0)

theorem fire_legal (p : Distribution α) (u v z : α)
    (hu : adj u z) (hv : adj v z)
    (havail : ∀ x, (if x = u then 1 else 0) + (if x = v then 1 else 0) ≤ p x) :
    LegalMove adj p (fire p u v z) := by
  refine ⟨u, v, z, hu, hv, ?_⟩
  intro x
  have hx := havail x
  simp only [fire]
  omega

/-- A batched ordinary transfer. Its realizability is proved below. -/
def transfer (p : Distribution α) (u z : α) (k : Nat) : Distribution α := fun x =>
  if x = u then p u - 2 * k else if x = z then p z + k else p x

theorem transfer_zero (p : Distribution α) (u z : α) : transfer p u z 0 = p := by
  funext x
  by_cases hu : x = u
  · subst x; simp [transfer]
  · by_cases hz : x = z
    · subst x; simp [transfer, hu]
    · simp [transfer, hu, hz]

theorem transfer_reachable (p : Distribution α) (u z : α)
    (hadj : adj u z) (hne : u ≠ z) (k : Nat) (hk : 2 * k ≤ p u) :
    Reachable adj p (transfer p u z k) := by
  induction k with
  | zero => rw [transfer_zero]; exact Reachable.refl p
  | succ k ih =>
    have hsmall : 2 * k ≤ p u := by omega
    refine Reachable.tail (ih hsmall) ⟨u, u, z, hadj, hadj, ?_⟩
    intro x
    by_cases hu : x = u
    · subst x; simp only [transfer, ↓reduceIte]
      have hzu : u ≠ z := hne
      simp only [hzu, ↓reduceIte]
      omega
    · by_cases hz : x = z
      · subst x
        simp only [transfer, hu, ↓reduceIte]
        omega
      · simp [transfer, hu, hz]

theorem transfer_pairs (p : Distribution α) (u z : α)
    (hadj : adj u z) (hne : u ≠ z) :
    ∃ q, Reachable adj p q ∧ q u = p u % 2 ∧
      q z = p z + p u / 2 ∧ (∀ x, x ≠ u → x ≠ z → q x = p x) := by
  let q := transfer p u z (p u / 2)
  refine ⟨q, transfer_reachable p u z hadj hne _ (by omega), ?_, ?_, ?_⟩
  · simp only [q, transfer, ↓reduceIte]; omega
  · simp [q, transfer, Ne.symm hne]
  · intro x hu hz; simp [q, transfer, hu, hz]

theorem LegalMove.add_right {p q : Distribution α} (hm : LegalMove adj p q)
    (s : Distribution α) : LegalMove adj (fun x => p x + s x) (fun x => q x + s x) := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := hm
  refine ⟨u, v, z, hu, hv, ?_⟩
  intro x
  have hx := hb x
  dsimp only
  omega

theorem Reachable.add_right {p q : Distribution α} (hseq : Reachable adj p q)
    (s : Distribution α) : Reachable adj (fun x => p x + s x) (fun x => q x + s x) := by
  induction hseq with
  | refl => exact Reachable.refl _
  | tail _ hm ih => exact Reachable.tail ih (hm.add_right s)

theorem TReachable.mono {p q : Distribution α} {r : α} {t : Nat}
    (hpq : ∀ x, p x ≤ q x) (hr : TReachable adj p r t) : TReachable adj q r t := by
  obtain ⟨p', hseq, ht⟩ := hr
  have heq : (fun x => p x + (q x - p x)) = q := by funext x; have := hpq x; omega
  have hseq' := hseq.add_right (fun x => q x - p x)
  rw [heq] at hseq'
  exact ⟨_, hseq', by omega⟩

/-- Collect the pebbles on a two-edge path toward one endpoint. -/
theorem path_delivers (p : Distribution α) (a b c : α)
    (hba : adj b a) (hcb : adj c b)
    (hab : a ≠ b) (hcbne : c ≠ b) (hac : a ≠ c) :
    ∃ q, Reachable adj p q ∧
      q a = p a + (p b + p c / 2) / 2 := by
  obtain ⟨q, hpq, _, hqb, hqother⟩ := transfer_pairs p c b hcb hcbne
  obtain ⟨s, hqs, _, hsa, _⟩ := transfer_pairs q b a hba (Ne.symm hab)
  have hqa := hqother a hac hab
  refine ⟨s, hpq.trans hqs, ?_⟩
  rw [hsa, hqa, hqb]

/-- Two distinct occupied neighbors can make a strict rubbling move. -/
theorem fire_legal_distinct (p : Distribution α) (u v z : α)
    (hu : adj u z) (hv : adj v z) (hne : u ≠ v)
    (hpu : 1 ≤ p u) (hpv : 1 ≤ p v) : LegalMove adj p (fire p u v z) := by
  apply fire_legal p u v z hu hv
  intro x
  by_cases hx : x = u
  · subst x; simpa [hne] using hpu
  · by_cases hy : x = v
    · subst x; simpa [Ne.symm hne] using hpv
    · simp [hx, hy]

/-- Pool two neighbors, including their odd leftover pebbles. -/
theorem two_neighbors_deliver (p : Distribution α) (a b c : α)
    (habedge : adj a b) (hcbedge : adj c b)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    ∃ q, Reachable adj p q ∧ q b = p b + (p a + p c) / 2 := by
  obtain ⟨q, hpq, hqa, hqb, hqother⟩ := transfer_pairs p a b habedge hab
  have hqc := hqother c (Ne.symm hac) hcb
  obtain ⟨s, hqs, hsc, hsb, hsother⟩ := transfer_pairs q c b hcbedge hcb
  have hsa : s a = p a % 2 := by rw [hsother a hac hab, hqa]
  have hsc' : s c = p c % 2 := by rw [hsc, hqc]
  have hsb' : s b = p b + p a / 2 + p c / 2 := by rw [hsb, hqb, hqc]
  by_cases hodd : 2 ≤ p a % 2 + p c % 2
  · have hpa : 1 ≤ s a := by omega
    have hpc : 1 ≤ s c := by omega
    have hm := fire_legal_distinct s a c b habedge hcbedge hac hpa hpc
    refine ⟨fire s a c b, Reachable.tail (hpq.trans hqs) hm, ?_⟩
    simp only [fire, Ne.symm hab, Ne.symm hcb, ↓reduceIte,
      Nat.add_zero, Nat.sub_zero]
    omega
  · refine ⟨s, hpq.trans hqs, ?_⟩
    omega

end RubblingFamily

#print axioms RubblingFamily.transfer_reachable
#print axioms RubblingFamily.transfer_pairs
#print axioms RubblingFamily.TReachable.mono

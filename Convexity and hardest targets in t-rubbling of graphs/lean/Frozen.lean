import CommonNeighbor

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

theorem Reachable.invariant_of_weight_eq {adj : α → α → Prop}
    {W : Distribution α → Nat} {P : Distribution α → Prop}
    (hmono : ∀ {p q}, LegalMove adj p q → W q ≤ W p)
    (hstep : ∀ {p q}, LegalMove adj p q → W q = W p → P p → P q)
    {p q : Distribution α} (hseq : Reachable adj p q) (heq : W q = W p)
    (hp : P p) : P q := by
  induction hseq with
  | refl => exact hp
  | @tail b c hab hbc ih =>
    have habw := weight_nonincreasing hmono hab
    have hbcw := hmono hbc
    have heb : W b = W p := by omega
    have hec : W c = W b := by omega
    exact hstep hbc hec (ih heb)

theorem levelWeight_cases (adj : α → α → Prop) [DecidableRel adj] (r x : α) :
    levelWeight adj r x = 1 ∨ levelWeight adj r x = 2 ∨ levelWeight adj r x = 4 := by
  unfold levelWeight
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

/-- Only the singleton s and the pile f are occupied among the far vertices. -/
def FrozenState (adj : α → α → Prop) [DecidableRel adj] (r s f : α)
    (p : Distribution α) : Prop :=
  p s = 1 ∧ ∀ x, levelWeight adj r x = 1 → x ≠ s → x ≠ f → p x = 0

/-- A weight-preserving move cannot use the isolated far singleton. -/
theorem frozen_source_not {adj : α → α → Prop} [DecidableRel adj]
    (r s f : α) (hsw : levelWeight adj r s = 1)
    (hdisjoint : ∀ z, levelWeight adj r z = 2 → ¬ (adj s z ∧ adj f z))
    {p q : Distribution α} (hP : FrozenState adj r s f p)
    (u v z : α) (hu : adj u z) (hv : adj v z)
    (hb : ∀ x, q x + (if x = u then 1 else 0) + (if x = v then 1 else 0) =
      p x + (if x = z then 1 else 0))
    (hcost : levelWeight adj r u + levelWeight adj r v = levelWeight adj r z) :
    u ≠ s := by
  intro hus
  subst u
  have hvc := levelWeight_cases adj r v
  have hzc := levelWeight_cases adj r z
  have hvw : levelWeight adj r v = 1 := by omega
  have hzw : levelWeight adj r z = 2 := by omega
  have hvz : v ≠ z := by intro h; subst z; omega
  have hsz : s ≠ z := by intro h; subst z; omega
  have hbv := hb v
  simp only [hvz, ↓reduceIte, Nat.add_zero] at hbv
  have hpv : 1 ≤ p v := by omega
  by_cases hvs : v = s
  · subst v
    have hsbal := hb s
    simp only [hsz, ↓reduceIte, Nat.add_zero] at hsbal
    have hps := hP.1
    omega
  · by_cases hvf : v = f
    · subst v; exact hdisjoint z hzw ⟨hu, hv⟩
    · have hzero := hP.2 v hvw hvs hvf
      omega

theorem frozen_step (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} [DecidableRel adj]
    (r s f : α) (hsw : levelWeight adj r s = 1)
    (hdisjoint : ∀ z, levelWeight adj r z = 2 → ¬ (adj s z ∧ adj f z))
    {p q : Distribution α} (hm : LegalMove adj p q)
    (heq : levelTotal L adj r q = levelTotal L adj r p)
    (hP : FrozenState adj r s f p) : FrozenState adj r s f q := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := hm
  have hbal := sumOn_weighted_balance L hn (levelWeight adj r) hb
  simp only [hcover, ↓reduceIte] at hbal
  have hcost : levelWeight adj r u + levelWeight adj r v = levelWeight adj r z := by
    unfold levelTotal at heq
    omega
  have hu' := frozen_source_not r s f hsw hdisjoint hP u v z hu hv hb hcost
  have hv' := frozen_source_not (p := p) (q := q) r s f hsw hdisjoint hP v u z hv hu
    (by intro x; have := hb x; omega) (by omega)
  have hup := levelWeight_pos adj r u
  have hvp := levelWeight_pos adj r v
  have hzfar : levelWeight adj r z ≠ 1 := by omega
  have hsz : s ≠ z := by intro h; subst z; exact hzfar hsw
  refine ⟨?_, ?_⟩
  · have hbs := hb s
    simp only [Ne.symm hu', Ne.symm hv', hsz, ↓reduceIte,
      Nat.add_zero] at hbs
    exact hbs.trans hP.1
  · intro x hxw hxs hxf
    have hxz : x ≠ z := by intro h; subst z; exact hzfar hxw
    have hbx := hb x
    rw [hP.2 x hxw hxs hxf] at hbx
    simp only [hxz, ↓reduceIte, Nat.add_zero] at hbx
    omega

theorem levelTotal_add (L : List α) (adj : α → α → Prop) [DecidableRel adj]
    (r : α) (p q : Distribution α) :
    levelTotal L adj r (fun x => p x + q x) = levelTotal L adj r p + levelTotal L adj r q := by
  simp only [levelTotal, Nat.mul_add, sumOn_add]

/-- The lower-bound obstruction used in case (3), for every positive t. -/
theorem frozen_pair_obstruction (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} [DecidableRel adj] (hloop : ∀ x, ¬ adj x x)
    (r s f : α) (hsw : levelWeight adj r s = 1) (hfw : levelWeight adj r f = 1)
    (hsf : s ≠ f)
    (hdisjoint : ∀ z, levelWeight adj r z = 2 → ¬ (adj s z ∧ adj f z))
    (t : Nat) (ht : 1 ≤ t) :
    ¬ TReachable adj (fun x => pile f (4 * t - 1) x + pile s 1 x) r t := by
  let p : Distribution α := fun x => pile f (4 * t - 1) x + pile s 1 x
  have hp : FrozenState adj r s f p := by
    refine ⟨?_, ?_⟩
    · simp [p, pile, hsf]
    · intro x _ hxs hxf; simp [p, pile, hxs, hxf]
  have hWp : levelTotal L adj r p = 4 * t := by
    dsimp only [p]
    rw [levelTotal_add, levelTotal_pile L hn hcover,
      levelTotal_pile L hn hcover, hfw, hsw]
    omega
  intro hreach
  obtain ⟨q, hseq, htarget⟩ := hreach
  change Reachable adj p q at hseq
  have hmono : ∀ {a b : Distribution α}, LegalMove adj a b →
      levelTotal L adj r b ≤ levelTotal L adj r a := levelTotal_move L hn hcover hloop r
  have hWq := weight_nonincreasing hmono hseq
  have hroot := levelTotal_root L hcover adj r q
  have heq : levelTotal L adj r q = levelTotal L adj r p := by omega
  have hQ := hseq.invariant_of_weight_eq hmono
    (frozen_step L hn hcover r s f hsw hdisjoint) heq hp
  have hrs : r ≠ s := by intro h; subst s; simp [levelWeight] at hsw
  have hpair := sumOn_two_bound L hn (fun x => levelWeight adj r x * q x)
    r s (hcover r) (hcover s) hrs
  have hrw : levelWeight adj r r = 4 := by simp [levelWeight]
  rw [hrw, hsw, hQ.1] at hpair
  change 4 * q r + 1 * 1 ≤ levelTotal L adj r q at hpair
  omega

end RubblingFamily

#print axioms RubblingFamily.frozen_pair_obstruction

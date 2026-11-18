import Std

/-!
The graph and rubbling semantics for the family manuscript.
No assumption of the manuscript's target-number formulas is made here.
-/
namespace RubblingFamily

inductive Vertex (m n : Nat) where
  | w
  | u (i : Fin (m + n))
  | v (i : Fin (m + n))
  deriving DecidableEq, Repr

/-- The first m indices are the C classes; the last n are the I classes. -/
def familyAdj {m n : Nat} : Vertex m n → Vertex m n → Prop
  | .w, .u _ => True
  | .u _, .w => True
  | .u i, .u j => i ≠ j ∧ (i.val < m ∨ j.val < m)
  | .v i, .v j => i ≠ j
  | .u i, .v j => i = j
  | .v i, .u j => i = j
  | _, _ => False

instance {m n : Nat} (x y : Vertex m n) : Decidable (familyAdj x y) := by
  cases x <;> cases y <;> unfold familyAdj <;> infer_instance

theorem familyAdj_symmetric {m n : Nat} (x y : Vertex m n) :
    familyAdj x y ↔ familyAdj y x := by
  cases x <;> cases y <;> simp [familyAdj, eq_comm, or_comm]

theorem familyAdj_irreflexive {m n : Nat} (x : Vertex m n) :
    ¬ familyAdj x x := by
  cases x <;> simp [familyAdj]

abbrev Distribution (α : Type) := α → Nat

/-- The manuscript's dot p(v): one at odd vertices and zero at even vertices. -/
abbrev dot {α : Type} (p : Distribution α) (v : α) : Nat := p v % 2

theorem dot_values {α : Type} (p : Distribution α) (v : α) :
    dot p v = 0 ∨ dot p v = 1 := by
  dsimp only [dot]
  omega

/-- Total size on exactly the vertices in Definition 2.1. -/
def familySize {m n : Nat} (p : Distribution (Vertex m n)) : Nat :=
  p .w + (List.ofFn (fun i => p (.u i))).sum +
    (List.ofFn (fun i => p (.v i))).sum

/-- Natural-number balance enforces availability, including two pebbles
when the sources coincide. The destination is adjacent to both sources. -/
def LegalMove {α : Type} [DecidableEq α] (adj : α → α → Prop)
    (p q : Distribution α) : Prop :=
  ∃ u v z, adj u z ∧ adj v z ∧
    ∀ x, q x + (if x = u then 1 else 0) + (if x = v then 1 else 0) =
      p x + (if x = z then 1 else 0)

/-- Reachability by a finite sequence of legal rubbling moves. -/
inductive Reachable {α : Type} [DecidableEq α] (adj : α → α → Prop) :
    Distribution α → Distribution α → Prop where
  | refl (p) : Reachable adj p p
  | tail {p q r} : Reachable adj p q → LegalMove adj q r → Reachable adj p r

def TReachable {α : Type} [DecidableEq α] (adj : α → α → Prop)
    (p : Distribution α) (root : α) (t : Nat) : Prop :=
  ∃ q, Reachable adj p q ∧ t ≤ q root

/-- A weight nonincreasing under individual moves is nonincreasing under
all finite executable sequences. -/
theorem weight_nonincreasing {α : Type} [DecidableEq α]
    {adj : α → α → Prop} {W : Distribution α → Nat}
    (hmove : ∀ {p q}, LegalMove adj p q → W q ≤ W p)
    {p q : Distribution α} (hseq : Reachable adj p q) : W q ≤ W p := by
  induction hseq with
  | refl => exact Nat.le_refl _
  | tail _ hmoveLast ih => exact Nat.le_trans (hmove hmoveLast) ih

/-- The soundness theorem for the manuscript's lower-bound weight method. -/
theorem not_t_reachable_of_weight {α : Type} [DecidableEq α]
    {adj : α → α → Prop} {W : Distribution α → Nat}
    {p : Distribution α} {root : α} {t C : Nat}
    (hmove : ∀ {p q}, LegalMove adj p q → W q ≤ W p)
    (hroot : ∀ q, C * q root ≤ W q) (hsmall : W p < C * t) :
    ¬ TReachable adj p root t := by
  intro ⟨q, hseq, htarget⟩
  have hmono := weight_nonincreasing hmove hseq
  have hweight := hroot q
  have htargetWeight := Nat.mul_le_mul_left C htarget
  omega

/-- An upper bound applies to every distribution of at least R pebbles. -/
def TargetUpperBound {α : Type} [DecidableEq α] (adj : α → α → Prop)
    (size : Distribution α → Nat) (root : α) (t R : Nat) : Prop :=
  ∀ p, R ≤ size p → TReachable adj p root t

/-- A certificate identifies the least threshold, not merely an upper bound. -/
def TargetNumberIs {α : Type} [DecidableEq α] (adj : α → α → Prop)
    (size : Distribution α → Nat) (root : α) (t R : Nat) : Prop :=
  TargetUpperBound adj size root t R ∧
    ∀ S, S < R → ¬ TargetUpperBound adj size root t S

/-- An upper-bound proof and one losing distribution of size R-1 certify
that R is the target t-rubbling number. -/
theorem target_number_of_bounds {α : Type} [DecidableEq α]
    {adj : α → α → Prop} {size : Distribution α → Nat}
    {root : α} {t R : Nat}
    (hupper : TargetUpperBound adj size root t R)
    (hlower : ∃ p, size p + 1 = R ∧ ¬ TReachable adj p root t) :
    TargetNumberIs adj size root t R := by
  refine ⟨hupper, ?_⟩
  intro S hS hupperS
  obtain ⟨p, hp, hnot⟩ := hlower
  exact hnot (hupperS p (by omega))

end RubblingFamily

#print axioms RubblingFamily.familyAdj_symmetric
#print axioms RubblingFamily.familyAdj_irreflexive
#print axioms RubblingFamily.weight_nonincreasing
#print axioms RubblingFamily.not_t_reachable_of_weight
#print axioms RubblingFamily.target_number_of_bounds

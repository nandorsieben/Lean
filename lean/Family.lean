import VITargets
import UITargets
import CliqueTargets

namespace RubblingFamily

/-- The four target values in Proposition 3.2 (m >= 1, n >= 2). -/
def targetValue (m n t : Nat) : Vertex m n → Nat
  | .w => 4*t+min (2*t) ((m+n+1)/3)
  | .u i => if i.val<m then 4*t else 4*t+1
  | .v i => if i.val<m then 4*t else 4*t+min (4*t) (n/2)

/-- Proposition 3.2: least thresholds for actual rubbling moves. -/
theorem target_formula {m n : Nat} (hm : 1≤m) (hn : 2≤n) (r : Vertex m n)
    (t : Nat) (ht : 1≤t) :
    TargetNumberIs familyAdj familySize r t (targetValue m n t r) := by
  cases r with
  | w => exact target_w (by omega) t ht
  | u i =>
    by_cases hic : i.val<m
    · simpa [targetValue,hic] using target_uc (by omega) i hic t ht
    · simpa [targetValue,hic] using target_ui hn i (by omega) t ht
  | v i =>
    by_cases hic : i.val<m
    · simpa [targetValue,hic] using target_vc i hic t ht
    · simpa [targetValue,hic] using target_vi hn i (by omega) t ht

def GraphUpperBound {α : Type} [DecidableEq α] (adj : α→α→Prop)
    (size : Distribution α→Nat) (t R : Nat) : Prop :=
  ∀r, TargetUpperBound adj size r t R

def GraphNumberIs {α : Type} [DecidableEq α] (adj : α→α→Prop)
    (size : Distribution α→Nat) (t R : Nat) : Prop :=
  GraphUpperBound adj size t R ∧ ∀ S, S<R → ¬GraphUpperBound adj size t S

theorem TargetNumberIs.unique {α : Type} [DecidableEq α]
    {adj : α→α→Prop} {size : Distribution α→Nat} {r : α} {t R S : Nat}
    (hR : TargetNumberIs adj size r t R) (hS : TargetNumberIs adj size r t S) : R=S := by
  by_cases h : R<S
  · exact False.elim (hS.2 R h hR.1)
  · by_cases h' : S<R
    · exact False.elim (hR.2 S h' hS.1)
    · omega

/-- Corollary 3.3: the graph-wide number for m >= 1, n >= 2, t >= 1. -/
theorem family_number {m n : Nat} (hm : 1≤m) (hn : 2≤n) (t : Nat) (ht : 1≤t) :
    GraphNumberIs (familyAdj (m:=m) (n:=n)) familySize t (proposedValue m n t) := by
  constructor
  · intro r p hp
    apply (target_formula hm hn r t ht).1 p
    have hvalue : targetValue m n t r ≤ proposedValue m n t := by
      cases r with
      | w => simp only [targetValue]; unfold proposedValue; omega
      | u i =>
        by_cases hic : i.val<m
        · simp only [targetValue,ite_eq_left hic]; unfold proposedValue; omega
        · simp only [targetValue,ite_eq_right hic]
          unfold proposedValue
          omega
      | v i =>
        by_cases hic : i.val<m <;> simp only [targetValue,hic,↓reduceIte]
        all_goals unfold proposedValue; omega
    omega
  · intro S hS hupper
    by_cases hcmp : min (2*t) ((m+n+1)/3) ≤ min (4*t) (n/2)
    · let i : Fin (m+n) := ⟨m,by omega⟩
      have hi : ¬i.val<m := by simp [i]
      have h := (target_formula hm hn (.v i) t ht).2 S
      apply h
      · simpa only [targetValue,ite_eq_right hi,proposedValue,Nat.max_eq_right hcmp] using hS
      · exact hupper (.v i)
    · have hcmp' : min (4*t) (n/2) ≤ min (2*t) ((m+n+1)/3) := by omega
      apply (target_formula hm hn .w t ht).2 S
      · simpa only [targetValue,proposedValue,Nat.max_eq_left hcmp'] using hS
      · exact hupper .w

/-- A vertex is hardest when its target threshold equals the proved graph threshold. -/
def IsHardestTarget (m n t : Nat) (r : Vertex m n) : Prop :=
  TargetNumberIs familyAdj familySize r t (proposedValue m n t)

/-- The manuscript's H_t^rho(G): a set of vertices, represented by its
membership predicate. Only positive demands are used in the paper. -/
abbrev Hρ (m n t : Nat) : Vertex m n → Prop := IsHardestTarget m n t

theorem hardest_iff_value {m n : Nat} (hm : 1≤m) (hn : 2≤n) (t : Nat) (ht : 1≤t)
    (r : Vertex m n) :
    IsHardestTarget m n t r ↔ targetValue m n t r=proposedValue m n t := by
  constructor
  · intro h; exact (target_formula hm hn r t ht).unique h
  · intro h; unfold IsHardestTarget; rw [←h]; exact target_formula hm hn r t ht

/-- The note after Corollary 3.3: eventual linearity with slope four.
The bound m+n is sufficient; no minimal threshold is asserted. -/
theorem family_eventually_linear {m n : Nat} (hm : 1≤m) (hn : 2≤n) :
    ∃ t₀ : Nat, 1≤t₀ ∧ ∀ t, t₀≤t →
      GraphNumberIs (familyAdj (m:=m) (n:=n)) familySize t
        (4*t+max ((m+n+1)/3) (n/2)) := by
  refine ⟨m+n,by omega,?_⟩
  intro t ht
  have h := family_number hm hn t (by omega)
  have hw : (m+n+1)/3≤2*t := by omega
  have hv : n/2≤4*t := by omega
  simpa only [proposedValue,Nat.min_eq_right hw,Nat.min_eq_right hv] using h

end RubblingFamily
#print axioms RubblingFamily.target_formula
#print axioms RubblingFamily.family_number
#print axioms RubblingFamily.family_eventually_linear

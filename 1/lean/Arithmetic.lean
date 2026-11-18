import Std

/-!
Arithmetic certificates for family.lyx.
These are unconditional arithmetic theorems, not yet the target rubbling formulas:
the graph-theoretic delivery and weight arguments must be connected separately.
Only Lean's standard library is required.
-/
namespace RubblingFamily

/-- Lemma 3.1(1), with the positive denominator explicit. -/
theorem floor_le_iff (x y d : Nat) (hd : 0 < d) :
    x / d ≤ y ↔ x ≤ d * y + d - 1 := by
  have h := Nat.div_le_iff_le_mul_add_pred (a := x) (c := y) hd
  have heq : d * y + (d - 1) = d * y + d - 1 := by omega
  simpa only [heq] using h

/-- Lemma 3.1(2). -/
theorem floor_three_bound (o : Nat) :
    o ≤ 2 * (o / 3) + (o + 1) / 3 + 1 := by omega

/-- The losing-distribution arithmetic in case (a), target w. -/
theorem w_upper_arithmetic (a b e o k t : Nat) (ho : o ≤ k)
    (hlose : a + (b + e + o / 3) / 2 < t) :
    a + b + 2 * e + o < 4 * t + min (2 * t) ((k + 1) / 3) := by
  have hround := floor_three_bound o
  omega

/-- The minimum-based lower-bound witness in case (a), target w. -/
theorem w_lower_parameters (k t : Nat) (hk : 2 ≤ k) (ht : 1 ≤ t) :
    let f := min (2 * t) ((k + 1) / 3)
    let o := 3 * f - 1
    2 ≤ o ∧ o ≤ k ∧
    (4 * t - 2 * f + 1) + (o - 1) = 4 * t + f - 1 ∧
    (3 * (4 * t - 2 * f + 1)) / 2 + (o - 1) = 6 * t - 1 := by
  dsimp
  omega

/-- The losing-distribution arithmetic in case (c), target utilde_i. -/
theorem ui_upper_arithmetic (a b c d t : Nat)
    (hlose : a + (b + c / 2 + d / 2) / 2 < t) :
    a + b + c + d ≤ 4 * t := by omega

/-- The losing-distribution arithmetic in case (d), target vtilde_i. -/
theorem vi_upper_arithmetic (a b d e o n t : Nat) (hn : 1 ≤ n)
    (ho : o ≤ n - 1)
    (hlose : a + (b + e + (d + o / 2) / 2) / 2 < t) :
    a + b + 2 * e + o + d < 4 * t + min (4 * t) (n / 2) := by
  -- Apply Lemma 3.1(1) to each of the two nested divisions.
  have hfirst : 2*a+b+e+(d+o/2)/2 ≤ 2*t-1 := by omega
  have hsecond : 4*a+2*b+2*e+d+o/2 ≤ 4*t-1 := by omega
  -- (o+1)/2 is ceil(o/2), bounded by both terms of the minimum.
  have hceil_t : (o+1)/2 ≤ 4*t := by omega
  have hceil_n : (o+1)/2 ≤ n/2 := by omega
  have hsplit : o = o/2+(o+1)/2 := by omega
  omega

/-- The minimum-based lower-bound witness in case (d), target vtilde_i. -/
theorem vi_lower_parameters (n t : Nat) (hn : 2 ≤ n) (ht : 1 ≤ t) :
    let f := min (4 * t) (n / 2)
    let o := 2 * f - 1
    1 ≤ o ∧ o ≤ n - 1 ∧
    (4 * t - f) + o = 4 * t + f - 1 ∧
    (4 * t - f) + o / 2 = 4 * t - 1 := by
  dsimp
  omega

/-- Proposition 4.1: the comparison that determines every hardest-target case. -/
theorem hardest_target_comparison (m n t : Nat)
    (hn : 6 ≤ n) (hk : 3 * (n / 2) + 2 ≤ m + n) (ht : 1 ≤ t) :
    (4 * t + 1 < n →
      min (2 * t) ((m + n + 1) / 3) < min (4 * t) (n / 2)) ∧
    ((n = 4 * t ∨ n = 4 * t + 1) →
      min (2 * t) ((m + n + 1) / 3) = min (4 * t) (n / 2)) ∧
    (n < 4 * t →
      min (4 * t) (n / 2) < min (2 * t) ((m + n + 1) / 3)) := by omega

/-- The numerical expression in Corollary 3.3; not a definition of rubbling. -/
def proposedValue (m n t : Nat) : Nat :=
  4 * t + max (min (2 * t) ((m + n + 1) / 3)) (min (4 * t) (n / 2))

/-- The claimed expression has the five values in Example 5.3. -/
theorem example_values :
    proposedValue 9 14 1 = 8 ∧ proposedValue 9 14 2 = 15 ∧
    proposedValue 9 14 3 = 19 ∧ proposedValue 9 14 4 = 24 ∧
    proposedValue 9 14 5 = 28 := by decide

/-- The expression violates discrete convexity and discrete concavity. -/
theorem example_nonconvex_nonconcave :
    proposedValue 9 14 1 + proposedValue 9 14 3 < 2 * proposedValue 9 14 2 ∧
    2 * proposedValue 9 14 3 < proposedValue 9 14 2 + proposedValue 9 14 4 := by decide

end RubblingFamily

#print axioms RubblingFamily.floor_le_iff
#print axioms RubblingFamily.floor_three_bound
#print axioms RubblingFamily.w_upper_arithmetic
#print axioms RubblingFamily.w_lower_parameters
#print axioms RubblingFamily.ui_upper_arithmetic
#print axioms RubblingFamily.vi_upper_arithmetic
#print axioms RubblingFamily.vi_lower_parameters
#print axioms RubblingFamily.hardest_target_comparison
#print axioms RubblingFamily.example_values
#print axioms RubblingFamily.example_nonconvex_nonconcave

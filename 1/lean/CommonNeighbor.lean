import Collect
import Boundary

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem sumOn_filter (L : List α) (P : α → Prop) [DecidablePred P] (p : α → Nat) :
    sumOn (L.filter fun x => decide (P x)) p = sumOn L (fun x => if P x then p x else 0) := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases hx : P x <;> simp [hx, ih]

/-- A coarse distance weight: target 4, neighbors 2, other vertices 1. -/
def levelWeight (adj : α → α → Prop) [DecidableRel adj] (r x : α) : Nat :=
  if x = r then 4 else if adj x r then 2 else 1

theorem levelWeight_pos (adj : α → α → Prop) [DecidableRel adj] (r x : α) :
    1 ≤ levelWeight adj r x := by
  unfold levelWeight
  split <;> (try split) <;> omega

theorem levelWeight_cost {adj : α → α → Prop} [DecidableRel adj]
    (hloop : ∀ x, ¬ adj x x) (r u v z : α) (hu : adj u z) (hv : adj v z) :
    levelWeight adj r z ≤ levelWeight adj r u + levelWeight adj r v := by
  by_cases hz : z = r
  · subst z
    have hur : u ≠ r := by intro h; subst u; exact hloop r hu
    have hvr : v ≠ r := by intro h; subst v; exact hloop r hv
    simp [levelWeight, hur, hvr, hu, hv]
  · have hpu := levelWeight_pos adj r u
    have hpv := levelWeight_pos adj r v
    have hzbound : levelWeight adj r z ≤ 2 := by
      simp only [levelWeight, hz, ↓reduceIte]
      split <;> omega
    omega

def levelTotal (L : List α) (adj : α → α → Prop) [DecidableRel adj]
    (r : α) (p : Distribution α) := sumOn L (fun x => levelWeight adj r x * p x)

theorem levelTotal_move (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} [DecidableRel adj] (hloop : ∀ x, ¬ adj x x) (r : α)
    {p q : Distribution α} (hm : LegalMove adj p q) :
    levelTotal L adj r q ≤ levelTotal L adj r p := by
  obtain ⟨u, v, z, hu, hv, hb⟩ := hm
  have hb' := sumOn_weighted_balance L hn (levelWeight adj r) hb
  simp only [hcover, ↓reduceIte] at hb'
  have hc := levelWeight_cost hloop r u v z hu hv
  unfold levelTotal
  omega

theorem levelTotal_root (L : List α) (hcover : ∀ x, x ∈ L)
    (adj : α → α → Prop) [DecidableRel adj] (r : α) (p : Distribution α) :
    4 * p r ≤ levelTotal L adj r p := by
  have h := member_le_sumOn L (fun x => levelWeight adj r x * p x) r (hcover r)
  simpa [levelWeight, levelTotal] using h

theorem sumOn_pile (L : List α) (hn : L.Nodup) (v : α) (hv : v ∈ L) (k : Nat) :
    sumOn L (pile v k) = k := by
  change sumOn L (fun x => if x = v then k else 0) = k
  rw [sumOn_indicator L hn v k, ite_eq_left hv]

theorem levelTotal_pile (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    (adj : α → α → Prop) [DecidableRel adj] (r v : α) (k : Nat) :
    levelTotal L adj r (pile v k) = levelWeight adj r v * k := by
  unfold levelTotal
  have h := sumOn_congr L (fun x => levelWeight adj r x * pile v k x)
    (fun x => if x = v then levelWeight adj r v * k else 0)
    (by intro x _; by_cases hx : x = v <;> simp [pile, hx])
  rw [h, sumOn_indicator L hn]
  simp [hcover]

/-- The common-neighbor upper bound, with executable routing of all far and near pebbles. -/
theorem common_neighbor_upper (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} [DecidableRel adj] (hloop : ∀ x, ¬ adj x x)
    (r c : α) (hcr : adj c r)
    (hcommon : ∀ x, x ≠ r → ¬ adj x r → adj x c) (t : Nat) :
    TargetUpperBound adj (sumOn L) r t (4 * t) := by
  intro p hp
  let N := L.filter fun x => decide (adj x r)
  let F := L.filter fun x => decide (x ≠ r ∧ ¬ adj x r)
  have hNn : N.Nodup := List.Pairwise.filter _ hn
  have hFn : F.Nodup := List.Pairwise.filter _ hn
  have hcF : c ∉ F := by simp [F, hcr]
  have hrF : r ∉ F := by simp [F]
  have hrN : r ∉ N := by simp [N, hloop r]
  have hcN : c ∈ N := by simp [N, hcover c, hcr]
  have hrc : r ≠ c := by intro h; subst c; exact hloop r hcr
  have hdisjoint : ∀ x, x ∈ N → x ∉ F := by
    intro x hx; simp only [N, List.mem_filter, decide_eq_true_eq] at hx
    simp [F, hx.2]
  obtain ⟨q, hpq, hqc, _, hother⟩ := collect_pairs F hFn c hcF
    (by intro x hx
        have hx' : x ≠ r ∧ ¬ adj x r := by simpa [F, hcover x] using hx
        exact hcommon x hx'.1 hx'.2) p
  have hqr := hother r hrF hrc
  have hNsum : sumOn N q = sumOn N p + sumOn F p / 2 := by
    have hpoint : ∀ x ∈ N, q x = p x + (if x = c then sumOn F p / 2 else 0) := by
      intro x hx
      by_cases hxc : x = c
      · subst x; simpa using hqc
      · simp [hxc, hother x (hdisjoint x hx) hxc]
    rw [sumOn_congr N _ _ hpoint, sumOn_add, sumOn_indicator N hNn]
    simp [hcN]
  have hsize : sumOn L p = p r + sumOn N p + sumOn F p := by
    have hpoint : ∀ x ∈ L, p x =
        (if x = r then p r else 0) + (if adj x r then p x else 0) +
        (if x ≠ r ∧ ¬ adj x r then p x else 0) := by
      intro x _
      by_cases hxr : x = r
      · subst x; simp [hloop r]
      · by_cases hnear : adj x r <;> simp [hxr, hnear]
    have hh := sumOn_congr L _ _ hpoint
    rw [sumOn_add, sumOn_add, sumOn_indicator L hn] at hh
    change sumOn L p = p r + sumOn (L.filter fun x => decide (adj x r)) p +
      sumOn (L.filter fun x => decide (x ≠ r ∧ ¬ adj x r)) p
    rw [sumOn_filter, sumOn_filter]
    simpa [hcover r] using hh
  obtain ⟨s, hqs, hsr, _, _⟩ := collect_pairs N hNn r hrN
    (by intro x hx; exact (List.mem_filter.mp hx).2 |> of_decide_eq_true) q
  refine ⟨s, hpq.trans hqs, ?_⟩
  omega

/-- A nonneighbor witnesses the matching lower bound for every positive t. -/
theorem common_neighbor_target (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} [DecidableRel adj] (hloop : ∀ x, ¬ adj x x)
    (r c : α) (hcr : adj c r)
    (hcommon : ∀ x, x ≠ r → ¬ adj x r → adj x c)
    (v : α) (hvr : v ≠ r) (hfar : ¬ adj v r) (t : Nat) (ht : 1 ≤ t) :
    TargetNumberIs adj (sumOn L) r t (4 * t) := by
  apply target_number_of_bounds (common_neighbor_upper L hn hcover hloop r c hcr hcommon t)
  refine ⟨pile v (4 * t - 1), ?_, ?_⟩
  · rw [sumOn_pile L hn v (hcover v)]; omega
  · apply not_t_reachable_of_weight (W := levelTotal L adj r) (C := 4)
      (levelTotal_move L hn hcover hloop r) (levelTotal_root L hcover adj r)
    rw [levelTotal_pile L hn hcover]
    simp only [levelWeight, hvr, hfar, ↓reduceIte, Nat.one_mul]
    omega

end RubblingFamily

#print axioms RubblingFamily.common_neighbor_target

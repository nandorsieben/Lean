import Collect

namespace RubblingFamily

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem sumOn_bool_filter (L : List α) (P : α → Bool) (p : α → Nat) :
    sumOn (L.filter P) p = sumOn L (fun x => if P x then p x else 0) := by
  induction L with
  | nil => rfl
  | cons x L ih => cases hx : P x <;> simp [hx, ih]

/-- The two-far-set upper-bound construction used for U_I targets. -/
theorem two_far_upper {adj : α → α → Prop} (N F₁ F₂ : List α)
    (hN : N.Nodup) (hF₁ : F₁.Nodup) (hF₂ : F₂.Nodup)
    (r c₁ c₂ : α) (hrN : r ∉ N) (hrF₁ : r ∉ F₁) (hrF₂ : r ∉ F₂)
    (hc₁ : c₁ ∈ N) (hc₂ : c₂ ∈ N)
    (hN₁ : ∀ x ∈ N, x ∉ F₁) (hN₂ : ∀ x ∈ N, x ∉ F₂)
    (h₁₂ : ∀ x ∈ F₁, x ∉ F₂)
    (hnear : ∀ x ∈ N, adj x r)
    (hroute₁ : ∀ x ∈ F₁, adj x c₁) (hroute₂ : ∀ x ∈ F₂, adj x c₂)
    (size : Distribution α → Nat)
    (hsize : ∀ p, size p = p r + sumOn N p + sumOn F₁ p + sumOn F₂ p) (t : Nat) :
    TargetUpperBound adj size r t (4 * t + 1) := by
  intro p hp
  have hrc₁ : r ≠ c₁ := by intro h; subst c₁; exact hrN hc₁
  have hrc₂ : r ≠ c₂ := by intro h; subst c₂; exact hrN hc₂
  obtain ⟨q, hpq, hqc₁, _, hother₁⟩ := collect_pairs F₁ hF₁ c₁
    (hN₁ c₁ hc₁) hroute₁ p
  have hqr := hother₁ r hrF₁ hrc₁
  have hNq := sumOn_single_change N F₁ hN c₁ hc₁ hN₁ p q _ hqc₁ hother₁
  have hF₂q : sumOn F₂ q = sumOn F₂ p := by
    apply sumOn_congr
    intro x hx
    apply hother₁
    · intro hxf₁; exact h₁₂ x hxf₁ hx
    · intro h; subst x; exact hN₂ c₁ hc₁ hx
  obtain ⟨s, hqs, hsc₂, _, hother₂⟩ := collect_pairs F₂ hF₂ c₂
    (hN₂ c₂ hc₂) hroute₂ q
  have hsr := hother₂ r hrF₂ hrc₂
  have hNs := sumOn_single_change N F₂ hN c₂ hc₂ hN₂ q s _ hsc₂ hother₂
  obtain ⟨v, hsv, hvr, _, _⟩ := collect_pairs N hN r hrN hnear s
  have htotal := hsize p
  refine ⟨v, (hpq.trans hqs).trans hsv, ?_⟩
  omega

end RubblingFamily

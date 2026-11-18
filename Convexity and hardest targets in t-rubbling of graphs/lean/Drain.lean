import Finite

namespace RubblingFamily
variable {α : Type} [DecidableEq α] {adj : α → α → Prop}

/-- Drain pairs along designated edges, retaining precisely the odd singletons. -/
theorem drain_pairs (S N : List α) (hS : S.Nodup) (hN : N.Nodup)
    (hdis : ∀ x ∈ S, x ∉ N) (sink : α → α)
    (hsink : ∀ x ∈ S, sink x ∈ N) (hadj : ∀ x ∈ S, adj x (sink x))
    (p : Distribution α) :
    ∃ q, Reachable adj p q ∧ (∀ x ∈ S, q x = p x % 2) ∧
      sumOn N q = sumOn N p + sumOn S (fun x => p x / 2) ∧
      (∀ x, x ∉ S → x ∉ N → q x = p x) := by
  induction S generalizing p with
  | nil => exact ⟨p, .refl p, by simp, by simp, by simp⟩
  | cons a S ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hS
    have haN := hdis a (by simp)
    have hsa := hsink a (by simp)
    have has : a ≠ sink a := by intro h; exact haN (h ▸ hsa)
    obtain ⟨b, hpb, hba, hbs, hbother⟩ :=
      transfer_pairs p a (sink a) (hadj a (by simp)) has
    have htail : ∀ x ∈ S, b x = p x := by
      intro x hx
      apply hbother
      · intro h; subst x; exact ha hx
      · intro h; exact hdis x (by simp [hx]) (h ▸ hsa)
    have hbN : sumOn N b = sumOn N p + p a / 2 :=
      sumOn_single_change N [a] hN (sink a) hsa
        (by
          intro x hx hmem
          have heq : x = a := by simpa using hmem
          exact haN (heq ▸ hx)) p b _ hbs
        (by intro x hx hxs; exact hbother x (by simpa using hx) hxs)
    obtain ⟨q, hbq, hqS, hqN, hqother⟩ := ih ht
      (by intro x hx; exact hdis x (by simp [hx]))
      (by intro x hx; exact hsink x (by simp [hx]))
      (by intro x hx; exact hadj x (by simp [hx])) b
    refine ⟨q, hpb.trans hbq, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hqother x ha haN, hba]
      · rw [hqS x hx, htail x hx]
    · have he := sumOn_congr S (fun x => b x / 2) (fun x => p x / 2)
        (by intro x hx; exact congrArg (fun k => k / 2) (htail x hx))
      rw [hqN, he, hbN, sumOn_cons]
      omega
    · intro x hx hxN
      have hxa : x ≠ a := by intro h; subst x; exact hx (by simp)
      have hxS : x ∉ S := by intro h; exact hx (by simp [h])
      rw [hqother x hxS hxN, hbother x hxa (by intro h; exact hxN (h ▸ hsa))]

end RubblingFamily
#print axioms RubblingFamily.drain_pairs

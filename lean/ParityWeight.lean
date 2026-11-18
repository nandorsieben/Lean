import Separable

namespace RubblingFamily
variable {α : Type} [DecidableEq α]

/-- Local balances certify a weight with a global floor of a parity count. -/
theorem parity_weight_move (L : List α) (hn : L.Nodup) (hcover : ∀ x, x ∈ L)
    {adj : α → α → Prop} (hloop : ∀ x, ¬ adj x x) (φ ψ : α → Nat → Nat)
    (hpair : ∀ u z a a' b b' A A' O O', adj u z → a'+2=a → b'=b+1 →
      A'+φ u a+φ z b=A+φ u a'+φ z b' →
      O'+ψ u a+ψ z b=O+ψ u a'+ψ z b' → A'+O'/2≤A+O/2)
    (hstrict : ∀ u v z a a' b b' c c' A A' O O',
      adj u z → adj v z → u≠v → a'+1=a → b'+1=b → c'=c+1 →
      A'+φ u a+φ v b+φ z c=A+φ u a'+φ v b'+φ z c' →
      O'+ψ u a+ψ v b+ψ z c=O+ψ u a'+ψ v b'+ψ z c' → A'+O'/2≤A+O/2)
    {p q : Distribution α} (hm : LegalMove adj p q) :
    sumOn L (fun x => φ x (q x)) + sumOn L (fun x => ψ x (q x))/2 ≤
    sumOn L (fun x => φ x (p x)) + sumOn L (fun x => ψ x (p x))/2 := by
  obtain ⟨u,v,z,hu,hv,hb⟩ := hm
  have huz : u≠z := by intro h; subst u; exact hloop z hu
  have hvz : v≠z := by intro h; subst v; exact hloop z hv
  by_cases huv : u=v
  · subst v
    have hbu := hb u
    have hbz := hb z
    simp only [huz, Ne.symm huz, ↓reduceIte, Nat.add_zero] at hbu hbz
    have hother : ∀ x, x≠u → x≠z → q x=p x := by
      intro x hx hz
      simpa [hx,hz] using hb x
    have hA := sumOn_local_two L hn hcover u z huz
      (fun x => φ x (p x)) (fun x => φ x (q x))
      (by intro x hx hz; exact congrArg (φ x) (hother x hx hz))
    have hO := sumOn_local_two L hn hcover u z huz
      (fun x => ψ x (p x)) (fun x => ψ x (q x))
      (by intro x hx hz; exact congrArg (ψ x) (hother x hx hz))
    exact hpair u z _ _ _ _ _ _ _ _ hu (by omega) (by omega) hA hO
  · have hbu := hb u
    have hbv := hb v
    have hbz := hb z
    simp only [huv, Ne.symm huv, huz, hvz, Ne.symm huz, Ne.symm hvz,
      ↓reduceIte, Nat.add_zero] at hbu hbv hbz
    have hother : ∀ x, x≠u → x≠v → x≠z → q x=p x := by
      intro x hx hy hz
      simpa [hx,hy,hz] using hb x
    have hA := sumOn_local_three L hn hcover u v z huv huz hvz
      (fun x => φ x (p x)) (fun x => φ x (q x))
      (by intro x hx hy hz; exact congrArg (φ x) (hother x hx hy hz))
    have hO := sumOn_local_three L hn hcover u v z huv huz hvz
      (fun x => ψ x (p x)) (fun x => ψ x (q x))
      (by intro x hx hy hz; exact congrArg (ψ x) (hother x hx hy hz))
    exact hstrict u v z _ _ _ _ _ _ _ _ _ _ hu hv huv (by omega) (by omega)
      (by omega) hA hO

inductive VICategory where
  | root | near | far1 | far2
  deriving DecidableEq

open VICategory

def viPhi : VICategory → Nat → Nat
  | root,a => 4*a
  | near,a => 2*a
  | far1,a => 2*(a/2)
  | far2,a => a
def viPsi : VICategory → Nat → Nat
  | far1,a => a%2
  | _,_ => 0

/-- Figure 3.3, row +1. The balance updates the total number of odd
vertices when the local count a increases. Both parities are before the change. -/
theorem far1_add_one (a o o' : Nat)
    (hparity : o' + a%2 = o + (a+1)%2) :
    Int.ofNat (2*((a+1)/2)+o'/2) - Int.ofNat (2*(a/2)+o/2) =
      Int.ofNat (a%2+o%2) := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Figure 3.3, row -1, with a pebble available at the vertex. -/
theorem far1_remove_one (a o o' : Nat) (ha : 1 ≤ a)
    (hparity : o' + a%2 = o + (a-1)%2) :
    Int.ofNat (2*((a-1)/2)+o'/2) - Int.ofNat (2*(a/2)+o/2) =
      Int.ofNat (a%2+o%2) - 2 := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Figure 3.3, row -2: removing a pair preserves the odd-vertex count. -/
theorem far1_remove_two (a o : Nat) (ha : 2 ≤ a) :
    Int.ofNat (2*((a-2)/2)+o/2) - Int.ofNat (2*(a/2)+o/2) = -2 := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- The source categories in Figure 3.2. The near case separates two far
sources from a move with at least one near or root source. Two far1 sources
at a near destination must coincide, because they have distinct matched neighbors. -/
def viAllowed (pair : Bool) (u v z : VICategory) : Prop :=
  match z with
  | root => u=near ∧ v=near
  | near => u=root ∨ u=near ∨ v=root ∨ v=near ∨
      (u=far2 ∧ v=far2) ∨ (pair=true ∧ u=far1 ∧ v=far1)
  | far1 => (u=near ∨ u=far2) ∧ (v=near ∨ v=far2)
  | far2 => True

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem vi_pair_numeric (u z : VICategory) (a a' b b' A A' O O' : Nat)
    (he : viAllowed true u u z) (ha : a'+2=a) (hb : b'=b+1)
    (hA : A'+viPhi u a+viPhi z b=A+viPhi u a'+viPhi z b')
    (hO : O'+viPsi u a+viPsi z b=O+viPsi u a'+viPsi z b') :
    A'+O'/2≤A+O/2 := by
  cases u <;> cases z <;> simp_all [viAllowed,viPhi,viPsi] <;> omega

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem vi_strict_numeric (u v z : VICategory) (a a' b b' c c' A A' O O' : Nat)
    (he : viAllowed false u v z) (ha : a'+1=a) (hb : b'+1=b) (hc : c'=c+1)
    (hA : A'+viPhi u a+viPhi v b+viPhi z c=A+viPhi u a'+viPhi v b'+viPhi z c')
    (hO : O'+viPsi u a+viPsi v b+viPsi z c=O+viPsi u a'+viPsi v b'+viPsi z c') :
    A'+O'/2≤A+O/2 := by
  cases u <;> cases v <;> cases z <;> simp_all [viAllowed,viPhi,viPsi] <;> omega

end RubblingFamily
#print axioms RubblingFamily.vi_strict_numeric
#print axioms RubblingFamily.far1_add_one
#print axioms RubblingFamily.far1_remove_one
#print axioms RubblingFamily.far1_remove_two

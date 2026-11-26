import Strips

namespace Lupanov

/-- Junctions at the interfaces of the blocks in Figure 8.3. -/
inductive Port (p s r : Nat) where
  | src
  | sink
  | lib (a : BitVec p) (i : Fin p) (w : BitVec s)
  | star (a : BitVec p) (z : BitVec r)
  | group (a : BitVec p)
  deriving DecidableEq

/-- A coloring is constant across each conducting connection at these interfaces. -/
def Compatible {m p s r : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (f : Fin (2^m) → BitVec p → BitVec r → Bool)
    (x : Fin (2^m)) (y : BitVec p) (z : BitVec r) (c : Port p s r → Bool) : Prop :=
  (∀ a i w, library hs hc i w x = true → c (.lib a i w) = c .src) ∧
  (∀ a t i, y.getLsbD i.val = !(a.getLsbD i.val) →
    c (.star a t) = c (.lib a i (mask f a t i))) ∧
  (∀ a, c (.group a) = c (.star a z)) ∧
  c .sink = c (.group (component hs hc x y))

/-- Undirected connectivity at the interfaces is precisely the desired truth value.
On a false input the separating cut colors every inactive copy uniformly. -/
theorem compatible_conducts {m p s r : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (f : Fin (2^m) → BitVec p → BitVec r → Bool)
    (x : Fin (2^m)) (y : BitVec p) (z : BitVec r) :
    (∀ c, Compatible hs hc f x y z c → c .src = c .sink) ↔ f x y z = true := by
  let a := component hs hc x y
  let i := stripe hs hc x
  have hmask (t : BitVec r) : library hs hc i (mask f a t i) x = f x y t := by
    simp [library, i, a, selected_mask]
  constructor
  · intro conducts
    let color : Port p s r → Bool
      | .src => true
      | .sink => f x y z
      | .lib b j w => if b = a then library hs hc j w x else true
      | .star b t => if b = a then f x y t else true
      | .group b => if b = a then f x y z else true
    apply Eq.symm
    apply conducts color
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b j w hw
      simp [color, hw]
    · intro b t j h
      by_cases hb : b = a
      · subst b
        have hj : j = i := (onComponent hs hc x y j).mp h
        subst j
        simp [color, hmask]
      · simp [color, hb]
    · intro b
      rfl
    · simp [color, a]
  · intro hf c ⟨lib, star, group, sink⟩
    have h₁ := lib a i (mask f a z i) ((hmask z).trans hf)
    have h₂ := star a z i ((onComponent hs hc x y i).mpr rfl)
    exact h₁.symm.trans (h₂.symm.trans ((group a).symm.trans sink.symm))

end Lupanov

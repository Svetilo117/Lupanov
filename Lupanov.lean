import Network
import Semantics
import Bounds

/-! # Lupanov's contact-circuit synthesis (Theorem 8.1)

The paper counts undirected literal-controlled contacts. A decoder has one
selected leaf, so its root can also be used as an output. We use one decoder
per strip/word in each component's library, one contact per arm of each
cofactor star, and the two stages of the output decoder from Fig. 8.3.
Duplicating zero words across strips only enlarges the library upper bound.
-/

namespace Lupanov

private def prefVar (r : Nat) {m p : Nat} (i : Fin (m+p)) := Fin.castAdd r i
private def rowVar (p r : Nat) {m : Nat} (i : Fin m) := prefVar (m := m) (p := p) r (Fin.castAdd p i)
private def shiftVar (m r : Nat) {p : Nat} (i : Fin p) := prefVar (m := m) (p := p) r (Fin.natAdd m i)
private def tailVar (m p : Nat) {r : Nat} (i : Fin r) := Fin.natAdd (m+p) i

section Construction
variable {m p s r : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
variable (f : Fin (2^m) → BitVec p → BitVec r → Bool)

private abbrev Circuit (m p s r : Nat) := Net (Fin (m+p+r)) (Port p s r)

/-- A library word gets its own contact tree. Its accepting leaves are
identified with the common source and all remaining leaves with its root. -/
private def libraryTree (a : BitVec p) (i : Fin p) (w : BitVec s) : Circuit m p s r :=
  Net.decoder (rowVar p r) (.lib a i w) fun u =>
    if library hs hc i w u.toFin then .src else .lib a i w

private def cofactorStar (a : BitVec p) (t : BitVec r) : Circuit m p s r :=
  Net.batch fun i => Net.contact (shiftVar m r i) (!(a.getLsbD i.val))
    (.star a t) (.lib a i (mask f a t i))

/-- The two-terminal network of §8, retaining names for the internal ports. -/
def synthesize : Circuit m p s r :=
  let libraries := Net.bits fun a => Net.batch fun i => Net.bits fun w =>
    libraryTree hs hc a i w
  let stars := Net.bits fun a => Net.bits fun t => cofactorStar f a t
  let tails := Net.bits fun a => Net.decoder (tailVar m p) (.group a) (.star a)
  let output := Net.decoder (prefVar (m := m) (p := p) r) .sink fun u =>
    .group (component hs hc (low u) (high u))
  Net.par libraries (Net.par stars (Net.par tails output))

theorem synthesize_cost :
    (synthesize hs hc f).cost ≤ (p+2)*2^(p+r) + (p*2^s+1)*2^(m+p+1) := by
  have lib := Net.cost_bits_le (fun a => Net.batch fun i => Net.bits fun w =>
      libraryTree (r := r) hs hc a i w) (fun a =>
    Net.cost_batch_le _ (fun i => Net.cost_bits_le _ (fun w =>
      Net.cost_decoder_le (rowVar p r) (.lib a i w : Port p s r) _)))
  have stars := Net.cost_bits_le (fun a => Net.bits fun t => cofactorStar (s := s) f a t)
    (fun a => Net.cost_bits_le _ (fun t => Net.cost_batch_le _ (fun i => Nat.le_refl 1)))
  have tails := Net.cost_bits_le (fun a => Net.decoder (tailVar m p)
      (.group a : Port p s r) (.star a))
    (fun a => Net.cost_decoder_le _ _ _)
  have output := Net.cost_decoder_le (prefVar (m := m) (p := p) r)
    (.sink : Port p s r) (fun u => .group (component hs hc (low u) (high u)))
  refine Nat.le_trans (Nat.add_le_add lib (Nat.add_le_add stars (Nat.add_le_add tails output))) ?_
  simp only [Nat.pow_add, Nat.pow_one, Nat.add_mul, Nat.one_mul]
  grind

theorem synthesize_correct (v : Fin (m+p+r) → Bool) :
    (synthesize hs hc f).Conducts v .src .sink ↔
      f (low (m := m) (p := p) (pack (fun i => v (prefVar r i))))
        (high (m := m) (p := p) (pack (fun i => v (prefVar r i))))
        (pack (fun i => v (tailVar m p i))) = true := by
  rw [← compatible_conducts hs hc]
  unfold Net.Conducts
  have constraints (c : Port p s r → Bool) :
      (synthesize hs hc f).Allows v c ↔ Compatible hs hc f
        (low (m := m) (p := p) (pack (fun i => v (prefVar r i))))
        (high (m := m) (p := p) (pack (fun i => v (prefVar r i))))
        (pack (fun i => v (tailVar m p i))) c := by
    simp [synthesize, libraryTree, cofactorStar, Compatible, apply_ite c,
      prefVar, rowVar, shiftVar, -BitVec.getLsbD_eq_getElem]
  simp only [constraints]

end Construction

/-- A two-terminal contact circuit on exactly n Boolean input variables. -/
structure ContactCircuit (n : Nat) where
  Vertex : Type
  net : Net (Fin n) Vertex
  source : Vertex
  sink : Vertex

def ContactCircuit.Realizes (C : ContactCircuit n) (f : (Fin n → Bool) → Bool) :=
  ∀ v, C.net.Conducts v C.source C.sink ↔ f v = true

/-- Theorem 8.1 in integer arithmetic. At any square-root scale d with
    d² ≤ n, the relative overhead above 2ⁿ/n is at most 200/d (for d > 0).
    In particular take the largest such d. -/
theorem synthesis_at_scale (n d : Nat) (hn : 1024 ≤ n) (hd : d*d ≤ n)
    (f : (Fin n → Bool) → Bool) :
    ∃ C : ContactCircuit n, C.Realizes f ∧ n*d*C.net.cost ≤ (d+200)*2^n := by
  obtain ⟨m,p,s,r,rfl,hs,hc,hsize⟩ := parameters n d hn hd
  let g x y z := f (joinInput (m := m) (p := p) (r := r) x y z)
  refine ⟨⟨Port p s r, synthesize hs hc g, .src, .sink⟩, ?_,
    Nat.le_trans (Nat.mul_le_mul_left _ (synthesize_cost hs hc g)) hsize⟩
  intro v
  simpa only [g, prefVar, tailVar, joinInput_reassemble] using synthesize_correct hs hc g v

/-- Integer square root, used to express the relative error without real division. -/
def floorSqrt : Nat → Nat
  | 0 => 0
  | n+1 =>
    let k := floorSqrt n
    if (k+1)*(k+1) ≤ n+1 then k+1 else k

theorem floorSqrt_spec (n : Nat) :
    floorSqrt n * floorSqrt n ≤ n ∧ n < (floorSqrt n+1)*(floorSqrt n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [floorSqrt]
    split <;> grind

/-- Theorem 8.1. Every Boolean function has a contact circuit. For n ≥ 1024
    its size is at most (2ⁿ/n)(1 + 200/⌊√n⌋), in cross-multiplied form. -/
theorem theorem_8_1 (n : Nat) (f : (Fin n → Bool) → Bool) :
    ∃ C : ContactCircuit n, C.Realizes f ∧
      (1024 ≤ n → n * floorSqrt n * C.net.cost ≤ (floorSqrt n + 200) * 2^n) := by
  by_cases hn : 1024 ≤ n
  · obtain ⟨C, realizes, size⟩ := synthesis_at_scale n _ hn (floorSqrt_spec n).1 f
    exact ⟨C, realizes, fun _ => size⟩
  · -- A single contact tree suffices below the asymptotic threshold.
    let leaf (w : BitVec n) := f (fun i => w.getLsbD i.val)
    refine ⟨⟨Bool, Net.decoder id false leaf, false, true⟩, ?_, fun h => (hn h).elim⟩
    intro v
    change (∀ c : Bool → Bool, (Net.decoder id false leaf).Allows v c → c false = c true) ↔ _
    simp only [Net.allows_decoder, id_eq, leaf, pack_bit]
    cases f v <;> simp
    exact ⟨id, by decide⟩

end Lupanov

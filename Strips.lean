import Std

/-! # The strip library and its regular translates (§§6–8)

The first block of variables is encoded by its truth-table row, starting at
zero. Bits of a library word are ordered from the least significant bit.
The last strip may contain fewer than `s` rows. -/

namespace Lupanov

/-- Pack a finite family of bits so that bit `i` contains entry `i`. -/
def pack {k : Nat} (b : Fin k → Bool) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn b)).cast (List.length_ofFn ..)

@[simp] theorem pack_bit {k : Nat} (b : Fin k → Bool) (i : Fin k) :
    (pack b).getLsbD i.val = b i := by
  unfold pack
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp)]
  simp

/-- The index of the consecutive height-`s` strip containing the given row. -/
def stripe {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s) (x : Fin (2^m)) : Fin p :=
  ⟨x.val / s, (Nat.div_lt_iff_lt_mul hs).2 (Nat.lt_of_lt_of_le x.isLt hc)⟩

/-- The characteristic functions of the strips take this one-hot value on strip `i`. -/
def pattern {p : Nat} (i : Fin p) : BitVec p := pack (fun j => decide (j = i))

@[simp] theorem pattern_bit {p : Nat} (i j : Fin p) :
    (pattern i).getLsbD j.val = decide (j = i) := pack_bit _ _

/-- The index of the unique translate of the regular component containing `(x,y)`. -/
def component {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (x : Fin (2^m)) (y : BitVec p) : BitVec p :=
  y ^^^ pattern (stripe hs hc x)

theorem in_component_iff {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (x : Fin (2^m)) (y a : BitVec p) :
    component hs hc x y = a ↔ y = a ^^^ pattern (stripe hs hc x) := by
  constructor
  · rintro rfl
    simp [component, BitVec.xor_assoc]
  · rintro rfl
    simp [component, BitVec.xor_assoc]

/-- Exactly one contact in each output star conducts on the selected component. -/
theorem active_iff {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (x : Fin (2^m)) (y : BitVec p) (i : Fin p) :
    (y.getLsbD i.val != (component hs hc x y).getLsbD i.val) = true ↔
      i = stripe hs hc x := by
  rw [component, BitVec.getLsbD_xor, pattern_bit]
  cases y.getLsbD i.val <;> by_cases h : i = stripe hs hc x <;> simp [h]

theorem onComponent {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (x : Fin (2^m)) (y : BitVec p) (i : Fin p) :
    (y.getLsbD i.val = !(component hs hc x y).getLsbD i.val) ↔
      i = stripe hs hc x := by
  rw [← active_iff hs hc x y i]
  cases y.getLsbD i.val <;> cases (component hs hc x y).getLsbD i.val <;> decide

/-- The member of the disjunctively universal library indexed by strip and word. -/
def library {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (i : Fin p) (word : BitVec s) (x : Fin (2^m)) : Bool :=
  decide (stripe hs hc x = i) && word.getLsbD (x.val % s)

/-- Encode the rows of a truth table lying in one strip. -/
def stripWord {m s p : Nat} (g : Fin (2^m) → Bool) (i : Fin p) : BitVec s :=
  pack fun j =>
    let r := s * i.val + j.val
    if h : r < 2^m then g ⟨r, h⟩ else false

theorem stripWord_bit {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (g : Fin (2^m) → Bool) (x : Fin (2^m)) :
    (stripWord (s := s) g (stripe hs hc x)).getLsbD (x.val % s) = g x := by
  let j : Fin s := ⟨x.val % s, Nat.mod_lt _ hs⟩
  change (pack _).getLsbD j.val = _
  rw [pack_bit]
  simp [j, stripe, Nat.div_add_mod, x.isLt]

/-- Lemma 6.1: the disjunction of one selected word per strip realizes `g`.
    The library has `p * 2^s` addresses (including duplicate zero words). -/
theorem disjunctively_universal {m s p : Nat} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (g : Fin (2^m) → Bool) (x : Fin (2^m)) :
    (∃ i : Fin p, library hs hc i (stripWord g i) x = true) ↔ g x = true := by
  constructor
  · rintro ⟨i, h⟩
    simp only [library, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hit⟩ := h
    rwa [stripWord_bit] at hit
  · intro h
    exact ⟨stripe hs hc x, by simpa [library, stripWord_bit] using h⟩

/-- Tabulate the cofactor on a single strip, padding unused rows with zero. -/
def mask {m s p : Nat} {T : Type} (f : Fin (2^m) → BitVec p → T → Bool)
    (a : BitVec p) (z : T) (i : Fin p) : BitVec s :=
  stripWord (fun x => f x (a ^^^ pattern i) z) i

/-- Equation (8.2) on the translate containing the input. -/
theorem selected_mask {m s p : Nat} {T : Type} (hs : 0 < s) (hc : 2^m ≤ p*s)
    (f : Fin (2^m) → BitVec p → T → Bool) (x : Fin (2^m)) (y : BitVec p) (z : T) :
    (mask (s := s) f (component hs hc x y) z (stripe hs hc x)).getLsbD (x.val % s)
      = f x y z := by
  rw [mask, stripWord_bit hs hc]
  simp [component, BitVec.xor_assoc]

/-- Decode the two contiguous blocks of a prefix address. -/
def low {m p : Nat} (w : BitVec (m+p)) : Fin (2^m) :=
  (pack (fun i : Fin m => w.getLsbD (i.castAdd p).val)).toFin

def high {m p : Nat} (w : BitVec (m+p)) : BitVec p :=
  pack (fun i : Fin p => w.getLsbD (i.natAdd m).val)

@[simp] theorem low_pack {m p : Nat} (v : Fin (m+p) → Bool) :
    low (pack v) = (pack (fun i : Fin m => v (i.castAdd p))).toFin := by
  unfold low
  simp only [pack_bit]

@[simp] theorem high_pack {m p : Nat} (v : Fin (m+p) → Bool) :
    high (pack v) = pack (fun i : Fin p => v (i.natAdd m)) := by
  unfold high
  simp only [pack_bit]

/-- Recover the original valuation from its row, regularity bits, and suffix. -/
def joinInput {m p r : Nat} (x : Fin (2^m)) (y : BitVec p) (z : BitVec r) :
    Fin (m+p+r) → Bool :=
  Fin.addCases (Fin.addCases (fun i => (BitVec.ofFin x).getLsbD i.val)
    (fun i => y.getLsbD i.val)) (fun i => z.getLsbD i.val)

theorem joinInput_reassemble (m p r : Nat) (v : Fin (m+p+r) → Bool) :
    joinInput (low (m := m) (p := p) (pack (fun i : Fin (m+p) => v (i.castAdd r))))
      (high (m := m) (p := p) (pack (fun i : Fin (m+p) => v (i.castAdd r))))
      (pack (fun i : Fin r => v (i.natAdd (m+p)))) = v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp only [low_pack, high_pack, joinInput, Fin.addCases_left, Fin.addCases_right,
        BitVec.ofFin_toFin, pack_bit]
  · simp only [joinInput, Fin.addCases_right, pack_bit]

end Lupanov

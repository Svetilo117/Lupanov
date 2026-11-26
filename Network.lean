import Strips

namespace Lupanov

@[simp] theorem pack_bits (w : BitVec k) : pack (fun i : Fin k => w.getLsbD i.val) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_bit _ ⟨i, hi⟩

private theorem pack_succ (f : Fin (k+1) → Bool) :
    pack f = BitVec.cons (f (Fin.last k)) (pack (fun i => f i.castSucc)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (pack f).getLsbD i = _ from pack_bit f ⟨i, hi⟩, BitVec.getLsbD_cons]
  by_cases h : i = k
  · subst i; simp; rfl
  · have hl : i < k := by omega
    simp [h, hl]
    exact (pack_bit (fun j : Fin k => f j.castSucc) ⟨i, hl⟩).symm

/-- Finite syntax of undirected contact networks with named boundary vertices.
    Mapping vertices identifies terminals; hiding quantifies out internal potentials. -/
inductive Net (I : Type) : Type → Type 1
  | empty : Net I V
  | wire (u v : V) : Net I V
  | contact (i : I) (b : Bool) (u v : V) : Net I V
  | par (A B : Net I V) : Net I V
  | map (f : V → W) (A : Net I V) : Net I W
  | hide (A : Net I (Sum V H)) : Net I V

namespace Net

/-- A closed contact enforces equality in both directions. A Boolean potential
    is constant on every conducting component. -/
@[simp] def Allows : Net I V → (I → Bool) → (V → Bool) → Prop
  | .empty, _, _ => True
  | .wire u v, _, c => c u = c v
  | .contact i b u v, x, c => x i = b → c u = c v
  | .par A B, x, c => A.Allows x c ∧ B.Allows x c
  | .map f A, x, c => A.Allows x (c ∘ f)
  | .hide A, x, c => ∃ d, A.Allows x (Sum.elim c d)

def Conducts (A : Net I V) (x : I → Bool) (u v : V) : Prop :=
  ∀ c, A.Allows x c → c u = c v

@[simp] def cost : Net I V → Nat
  | .empty | .wire .. => 0
  | .contact .. => 1
  | .par A B => A.cost + B.cost
  | .map _ A | .hide A => A.cost

def batch : {n : Nat} → (Fin n → Net I V) → Net I V
  | 0, _ => .empty
  | _+1, A => .par (A 0) (batch (fun i => A i.succ))

@[simp] theorem allows_batch (A : Fin n → Net I V) :
    (batch A).Allows x c ↔ ∀ i, (A i).Allows x c := by
  induction n with
  | zero => simp [batch]; exact fun i => i.elim0
  | succ n ih => simp [batch, ih, Fin.forall_fin_succ]

theorem cost_batch_le (A : Fin n → Net I V) (h : ∀ i, (A i).cost ≤ b) :
    (batch A).cost ≤ n*b := by
  induction n with
  | zero => simp [batch]
  | succ n ih =>
    simpa [batch, Nat.succ_mul, Nat.add_comm] using
      Nat.add_le_add (h 0) (ih (fun i => A i.succ) (fun i => h i.succ))

def bits (A : BitVec k → Net I V) : Net I V := batch (fun i => A (BitVec.ofFin i))

@[simp] theorem allows_bits (A : BitVec k → Net I V) :
    (bits A).Allows x c ↔ ∀ i, (A i).Allows x c := by
  simp only [bits, allows_batch]
  exact ⟨fun h i => h i.toFin, fun h i => h _⟩

theorem cost_bits_le (A : BitVec k → Net I V) (h : ∀ i, (A i).cost ≤ b) :
    (bits A).cost ≤ 2^k*b := cost_batch_le _ (fun i => h (.ofFin i))

/-- Tree with complementary contacts on its two branches at every fork. -/
def decoder : {k : Nat} → (Fin k → I) → V → (BitVec k → V) → Net I V
  | 0, _, root, leaf => .wire root (leaf 0)
  | k+1, var, root, leaf =>
    let branch (b : Bool) : Net I (V ⊕ Bool) :=
      .par (.contact (var (Fin.last k)) b (.inl root) (.inr b))
        (decoder (fun i => var i.castSucc) (.inr b) (fun w => .inl (leaf (w.cons b))))
    .hide (.par (branch false) (branch true))

@[simp] theorem allows_decoder (var : Fin k → I) (root : V) (leaf : BitVec k → V) :
    (decoder var root leaf).Allows x c ↔ c root = c (leaf (pack (fun i => x (var i)))) := by
  induction k generalizing V with
  | zero => simp [decoder, Subsingleton.elim (pack _) (0 : BitVec 0)]
  | succ k ih =>
    simp only [decoder, Allows, ih, Sum.elim_inl, Sum.elim_inr]
    rw [pack_succ]
    cases e : x (var (Fin.last k)) <;> simp
    all_goals
      constructor
      · rintro ⟨d, h₁, h₂⟩; grind
      · intro h
        refine ⟨fun b => c (leaf ((pack (fun i : Fin k => x (var i.castSucc))).cons b)), ?_⟩
        simp [h]

theorem cost_decoder_exact (var : Fin k → I) (root : V) (leaf : BitVec k → V) :
    (decoder var root leaf).cost + 2 = 2^(k+1) := by
  induction k generalizing V with
  | zero => rfl
  | succ k ih =>
    simp only [decoder, cost]
    have h (b : Bool) := ih (fun i => var i.castSucc) (Sum.inr b : V ⊕ Bool)
      (fun w => Sum.inl (leaf (w.cons b)))
    rw [Nat.pow_succ]
    have := h false
    have := h true
    omega

theorem cost_decoder_le (var : Fin k → I) (root : V) (leaf : BitVec k → V) :
    (decoder var root leaf).cost ≤ 2^(k+1) := by
  have := cost_decoder_exact var root leaf; omega

/-! ## Path semantics

Expand every hidden vertex into a fresh internal vertex. The resulting list of
closed edges gives the ordinary undirected graph of the circuit at an input. -/

variable {W U : Type}

/-- Internal vertices from distinct subcircuits are disjoint. -/
def Internal : Net I V → Type
  | .empty | .wire .. | .contact .. => Empty
  | .par A B => A.Internal ⊕ B.Internal
  | .map _ A => A.Internal
  | .hide (H := H) A => H ⊕ A.Internal

/-- List the edges conducting at this input after naming all the vertices. -/
def closedEdges (A : Net I V) (x : I → Bool) (port : V → W) (inner : A.Internal → W) :
    List (W × W) :=
  match A with
  | .empty => []
  | .wire u v => [(port u, port v)]
  | .contact i b u v => if x i = b then [(port u, port v)] else []
  | .par A B =>
    A.closedEdges x port (inner ∘ Sum.inl) ++ B.closedEdges x port (inner ∘ Sum.inr)
  | .map f A => A.closedEdges x (port ∘ f) inner
  | .hide A => A.closedEdges x (Sum.elim port (inner ∘ Sum.inl)) (inner ∘ Sum.inr)

/-- A potential assigns equal colors to the ends of each closed edge. -/
def Monochrome (edges : List (W × W)) (color : W → Bool) :=
  ∀ e ∈ edges, color e.1 = color e.2

private theorem monochrome_append {a b : List (W × W)} :
    Monochrome (a ++ b) c ↔ Monochrome a c ∧ Monochrome b c := by
  simp [Monochrome, or_imp, forall_and]

/-- Renaming all vertices cannot change the cut constraints pulled back along that map. -/
private theorem closedEdges_map (A : Net I V) (x : I → Bool)
    (port : V → W) (inner : A.Internal → W) (f : W → U) :
    (A.closedEdges x port inner).map (Prod.map f f) =
      A.closedEdges x (f ∘ port) (f ∘ inner) := by
  induction A generalizing U W with
  | empty | wire => rfl
  | contact i b u v => by_cases h : x i = b <;> simp [closedEdges, h]
  | par A B ha hb => simp [closedEdges, List.map_append, ha, hb]; rfl
  | map g A ha => exact ha _ _ _
  | hide A ha =>
    rw [closedEdges, closedEdges, ha]
    congr 1
    funext v
    cases v <;> rfl

private theorem mono_colors (A : Net I V) (x : I → Bool) (port : V → W)
    (inner : A.Internal → W) (color : W → Bool) :
    Monochrome (A.closedEdges x port inner) color ↔
      Monochrome (A.closedEdges x (color ∘ port) (color ∘ inner)) id := by
  rw [← closedEdges_map]
  constructor
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact h d hd
  · intro h e he
    exact h _ (List.mem_map.mpr ⟨e, he, rfl⟩)

private theorem allows_iff_internal (A : Net I V) (x : I → Bool) (c : V → Bool) :
    A.Allows x c ↔ ∃ d, Monochrome (A.closedEdges x c d) id := by
  induction A with
  | empty =>
    exact ⟨fun _ => ⟨Empty.elim, by simp [closedEdges, Monochrome]⟩, fun _ => trivial⟩
  | wire u v =>
    simp [Allows, closedEdges, Monochrome]
  | contact i b u v =>
    by_cases h : x i = b <;> simp [Allows, closedEdges, Monochrome, h]
  | par A B ha hb =>
    simp only [Allows, ha, hb, closedEdges, monochrome_append]
    constructor
    · rintro ⟨⟨a, ea⟩, ⟨b, eb⟩⟩
      exact ⟨Sum.elim a b, ea, eb⟩
    · rintro ⟨d, ea, eb⟩
      exact ⟨⟨_, ea⟩, ⟨_, eb⟩⟩
  | map g A ha => exact ha _
  | hide A ha =>
    simp only [Allows, ha, closedEdges]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨Sum.elim a b, h⟩
    · rintro ⟨d, h⟩
      exact ⟨_, _, h⟩

/-- The two orientations of each conducting edge can occur in a walk. -/
inductive Walk (edges : List (W × W)) (start : W) : W → Prop
  | refl : Walk edges start start
  | forward : Walk edges start u → (u, v) ∈ edges → Walk edges start v
  | backward : Walk edges start u → (v, u) ∈ edges → Walk edges start v

theorem walk_iff_cuts (edges : List (W × W)) (u v : W) :
    Walk edges u v ↔ ∀ c, Monochrome edges c → c u = c v := by
  classical
  constructor
  · intro path c hc
    induction path with
    | refl => rfl
    | forward _ e ih => exact ih.trans (hc _ e)
    | backward _ e ih => exact ih.trans (hc _ e).symm
  · intro cuts
    let reachable (v : W) := decide (Walk edges u v)
    have hc : Monochrome edges reachable := by
      rintro ⟨a,b⟩ h
      exact decide_eq_decide.mpr ⟨fun p => .forward p h, fun p => .backward p h⟩
    have eq := cuts reachable hc
    have start : reachable u = true := decide_eq_true (.refl : Walk edges u u)
    exact of_decide_eq_true (eq.symm.trans start)

/-- The cut-based semantics used during synthesis is ordinary two-terminal reachability. -/
theorem conducts_iff_walk (A : Net I V) (x : I → Bool) (u v : V) :
    A.Conducts x u v ↔
      Walk (A.closedEdges x Sum.inl Sum.inr) (Sum.inl u : V ⊕ A.Internal) (Sum.inl v) := by
  rw [walk_iff_cuts]
  constructor
  · intro h c hc
    exact h (c ∘ Sum.inl) ((allows_iff_internal ..).2
      ⟨c ∘ Sum.inr, (mono_colors ..).1 hc⟩)
  · intro h c hc
    obtain ⟨d, hd⟩ := (allows_iff_internal ..).1 hc
    let color := Sum.elim c d
    exact h color ((mono_colors ..).2 hd)

end Net
end Lupanov

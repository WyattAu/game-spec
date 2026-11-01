/-
GameSpec.Tumbleweed — formal model of CodeCup 2027 Tumbleweed.

Iteration 1 scope: the board geometry (axial hex coordinates), sightlines,
placement, and the keystone congruence theorem — *placing a stack on cell c
does not change what any ray from c sees*. That theorem is the technical
foundation for the no-suicide rule: the opponent can never immediately
recapture, because your sightline count at c is fixed by the pre-placement
board.

Model decisions (Iteration 1 research):
- Cells are **axial coordinates** (q, r : ℤ) per the canonical hex-grid
  treatment (Red Blob Games, "Hexagonal Grids"): the six neighbour steps are
  the same unit vectors everywhere on the grid, which makes ray reasoning a
  coordinate-induction instead of a case analysis per board region.
- The CodeCup labels map as col = r + q, row = q; board membership is then
  `1 ≤ q ≤ 11 ∧ 1 ≤ r + q ≤ 11 ∧ |r| ≤ 5`. The mapping is validated against
  the official sample game (red B2 → E5 is a sightline: both have r = −2).
- Rays are bounded folds over offsets k = 1..10 (the board's diameter bound)
  — structurally terminating, no well-founded recursion needed.
- Board is a total function `Cell → Stack`; placement is a function update.
-/

import GameSpec.Axial

namespace Tw

/-! ## Colors and stacks -/

inductive Color where
  | empty | red | white | neutral
deriving BEq, DecidableEq, Repr

/-- The opposing colour (identity for empty/neutral). An involution on
ALL colours — relied on by `no_immediate_recapture`. -/
def other : Color → Color
  | .red => .white
  | .white => .red
  | c => c

theorem other_other (c : Color) : other (other c) = c := by
  cases c <;> rfl

structure Stack where
  color : Color
  value : Int

/-- A board is the full stack assignment. Finiteness is implicit: every
position starts empty and `place` updates one cell at a time. -/
def Board := Cell → Stack

def emptyStack : Stack := { color := .empty, value := 0 }

def emptyBoard : Board := fun _ => emptyStack

/-- Placing stack `s` on cell `c`. -/
def place (b : Board) (c : Cell) (s : Stack) : Board :=
  fun x => if x = c then s else b x

/-! ## Sightlines -/

/-- One fold step of a sightline ray: keep the first hit, or look at the
next offset — off-board offsets end the ray with no hit. -/
def rayStep (b : Board) (cell : Cell) (st : Option Color) : Option Color :=
  match st with
  | some col => some col
  | none =>
    if onBoardB cell then
      let s := b cell
      if s.color = Color.empty then none else some s.color
    else none

/-- The colour a stack at cell `c` sees along direction `d`: walk offsets
k = 1..10 (the board's diameter bound — **k = 0 is the origin itself and is
excluded**, else a placed stack would see itself) and take the first
non-empty stack's colour; no hit → empty. -/
def firstHit (b : Board) (d : Dir) (c : Cell) : Color :=
  (List.range' 1 10).foldl (fun st k => rayStep b (offset c d k) st) none
  |>.getD .empty

/-- How many friendly stacks the cell `c` sees: one per direction whose
first hit has the given colour. -/
def seen (b : Board) (color : Color) (c : Cell) : Nat :=
  (Dir.all.map (fun d => if firstHit b d c = color then 1 else 0)).sum

/-! ## The keystone congruence -/

/-- Single-step congruence: boards agreeing *at the read cell* agree on
the ray step there. -/
theorem rayStep_congr_at (b b' : Board) (cell : Cell) (st : Option Color)
    (hag : b cell = b' cell) :
    rayStep b cell st = rayStep b' cell st := by
  cases st with
  | some col => rfl
  | none => simp only [rayStep, hag]

/-- **Fold congruence**: the bounded ray walk only reads offsets of `cc`,
all distinct from `cc` (`offset_ne`), so boards agreeing off `cc` agree on
every step. -/
theorem firstHitStep_foldl_congr (b b' : Board) (cc : Cell) (d : Dir)
    (hag : ∀ x, x ≠ cc → b x = b' x) :
    ∀ (ks : List Nat), (∀ k ∈ ks, 1 ≤ k) → ∀ (st : Option Color),
      (ks.foldl (fun st k => rayStep b (offset cc d k) st) st) =
      (ks.foldl (fun st k => rayStep b' (offset cc d k) st) st) := by
  intro ks
  induction ks with
  | nil => intro _ _; rfl
  | cons k ks ih =>
    intro hmem st
    have hk1 : 1 ≤ k := hmem k (List.mem_cons_self ..)
    have hrest : ∀ j ∈ ks, 1 ≤ j := fun j hj => hmem j (List.mem_cons_of_mem _ hj)
    simp only [List.foldl_cons]
    have hstep : rayStep b (offset cc d k) st = rayStep b' (offset cc d k) st :=
      rayStep_congr_at b b' (offset cc d k) st
        (hag (offset cc d k) (offset_ne cc d k hk1))
    rw [hstep, ih hrest (rayStep b' (offset cc d k) st)]

/-- **firstHit congruence**. -/
theorem firstHit_congr (b b' : Board) (cc : Cell)
    (hag : ∀ x, x ≠ cc → b x = b' x) :
    ∀ d, firstHit b d cc = firstHit b' d cc := by
  intro d
  unfold firstHit
  have hfold : (List.range' 1 10).foldl (fun st k => rayStep b (offset cc d k) st) none =
      (List.range' 1 10).foldl (fun st k => rayStep b' (offset cc d k) st) none :=
    firstHitStep_foldl_congr b b' cc d hag (List.range' 1 10)
      (fun k hk => by simp [List.mem_range'] at hk; omega) none
  rw [hfold]

/-- Core-only replacement for `List.map_congr` (which is mathlib). -/
theorem sum_map_congr (b b' : Board) (color : Color) (c : Cell)
    (hag : ∀ x, x ≠ c → b x = b' x) :
    ∀ (ds : List Dir),
      (ds.map (fun d => if firstHit b d c = color then 1 else 0)).sum =
      (ds.map (fun d => if firstHit b' d c = color then 1 else 0)).sum := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [firstHit_congr b b' c hag d, ih]

/-- **seen congruence** — the keystone. Two boards that agree everywhere
except possibly at `c` give cell `c` the same sightline counts. -/
theorem seen_congr (b b' : Board) (color : Color) (c : Cell)
    (hag : ∀ x, x ≠ c → b x = b' x) :
    seen b color c = seen b' color c := by
  unfold seen
  exact sum_map_congr b b' color c hag Dir.all

/-- **Corollary (seen_place_self)**: placing a stack on `c` — whatever its
colour or value — leaves `c`'s sightline counts untouched. This is the
fact that makes the no-suicide rule airtight (Iteration 2). -/
theorem seen_place_self (b : Board) (c : Cell) (s : Stack) (color : Color) :
    seen (place b c s) color c = seen b color c := by
  apply seen_congr
  intro x hx
  simp only [place]
  split
  · next h => exact absurd h hx
  · rfl

/-! ## The total value — the fill-termination measure (Iteration 5)

Every legal placement strictly increases the total value on the board:
an empty-cell placement adds `value = seen ≥ 1`; a capture/upgrade
replaces a stack with a strictly larger one. The total is bounded above
(≤ 6 per cell × 91 cells), so fuel-bounded fill saturates. -/

/-- Per-cell value agreement: placement changes only cell `c`. -/
theorem place_value_ne (b : Board) (c : Cell) (s : Stack) (x : Cell) (hx : x ≠ c) :
    (place b c s x).value = (b x).value := by
  simp only [place, if_neg hx]

/-- General ≤: pointwise-bounded maps have bounded sums. -/
theorem sum_map_le (f g : Cell → Nat) (l : List Cell)
    (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hrest : (rest.map f).sum ≤ (rest.map g).sum :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hhead : f a ≤ g a := h a (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- General strict: pointwise ≤ with one strict member gives a strict sum. -/
theorem sum_map_lt (f g : Cell → Nat) (l : List Cell)
    (h : ∀ x ∈ l, f x ≤ g x) (c : Cell) (hc : c ∈ l) (hlt : f c < g c) :
    (l.map f).sum < (l.map g).sum := by
  induction l generalizing c with
  | nil => cases hc
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = c
    · subst ha
      have hrest : ∀ x ∈ rest, f x ≤ g x :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hsum := sum_map_le f g rest hrest
      simp only [List.mem_cons, List.map_cons, List.sum_cons] at hc ⊢
      omega
    · have hrest : ∀ x ∈ rest, f x ≤ g x :=
        fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hmem : c ∈ rest := by
        rcases List.mem_cons.mp hc with heq | hm
        · exact absurd heq.symm ha
        · exact hm
      have hstrict := ih hrest c hmem hlt
      have hhead : f a ≤ g a := h a (List.mem_cons_self ..)
      omega

/-- All 91 board cells in scan order (columns A–K outer, rows inner — our
approximation of the judge's fill order, which is unpublished). -/
def cellList : List Cell :=
  (List.range 11).flatMap fun (i : Nat) =>
    (List.range 11).filterMap fun (j : Nat) =>
      let q : Int := (i : Int) + 1
      let rr : Int := (j : Int) - (i : Int)
      let c : Cell := { q := q, r := rr }
      if onBoardB c then some c else none

/-- The total value on the board: the sum of `natAbs` values over all
cells. Empty cells contribute 0 (well-formed boards). -/
def totalValue (b : Board) : Nat :=
  (cellList.map (fun x => (b x).value.natAbs)).sum

/-- Core-only: a constant map's sum is the constant times the length. -/
theorem sum_map_const (k : Nat) (l : List Cell) :
    (l.map (fun _ => k)).sum = k * l.length := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [ih, Nat.mul_add, Nat.add_comm]

/-- The total value of any board whose stacks are all worth ≤ 6 is at
most 6 × (number of cells) = 546. -/
theorem totalValue_le_bound (b : Board)
    (hb : ∀ x ∈ cellList, (b x).value.natAbs ≤ 6) :
    totalValue b ≤ 6 * cellList.length := by
  unfold totalValue
  have h := sum_map_le (fun x => (b x).value.natAbs) (fun _ => 6) cellList hb
  rw [sum_map_const] at h
  exact h

/-- The placement's value at `c` is the auto-determined count. -/
theorem place_value_self (b : Board) (c : Cell) (s : Stack) :
    (place b c s c).value = s.value := by
  simp [place]

/-- A placement preserves the empty-cells-carry-zero invariant away from
the placed stack, which is non-empty by construction. -/
theorem place_zero_ok (b : Board) (c : Cell) (s : Stack)
    (hs : s.color ≠ Color.empty)
    (hz : ∀ x, (b x).color = Color.empty → (b x).value = 0) :
    ∀ x, (place b c s x).color = Color.empty → (place b c s x).value = 0 := by
  intro x hx
  simp only [place] at hx ⊢
  revert hx
  split
  · intro hx; exact absurd hx hs
  · intro hx; exact hz x hx

/-- A placement preserves the value bound: the placed stack's value is
the auto-determined sightline count, ≤ 6. -/
theorem place_bound_ok (b : Board) (c : Cell) (s : Stack)
    (hs : s.value.natAbs ≤ 6)
    (hb : ∀ x, (b x).value.natAbs ≤ 6) :
    ∀ x, (place b c s x).value.natAbs ≤ 6 := by
  intro x
  simp only [place]
  by_cases hxc : x = c
  · rw [if_pos hxc]
    exact hs
  · rw [if_neg hxc]
    exact hb x

/-! ## Placement legality and the no-recapture theorem -/

/-- Placement legality, CodeCup variant: on-board, sees at least one
friend, **no immediate recapture** (no suicide — your sightline count must
be at least the opponent's), and a capture/upgrade needs the new value
strictly greater than the target's. -/
def legalPlacement (b : Board) (me : Color) (c : Cell) : Prop :=
  onBoard c ∧
  seen b me c ≥ 1 ∧
  seen b me c ≥ seen b (other me) c ∧
  ((b c).color = Color.empty ∨ (b c).value < seen b me c)

/-- **The no-recapture theorem** — the no-suicide rule's teeth. After a
legal placement (placed value = your pre-placement count), the opponent's
sightline count at `c` is at most yours — so they cannot capture: a
capture needs a count strictly greater than your stack's value. The
two `seen_place_self` rewrites are the entire proof. -/
theorem no_immediate_recapture (b : Board) (me : Color) (c : Cell)
    (hge : seen b (other me) c ≤ seen b me c) :
    seen (place b c { color := me, value := seen b me c }) (other me) c
      ≤ seen (place b c { color := me, value := seen b me c }) me c := by
  rw [seen_place_self b c _ (other me), seen_place_self b c _ me]
  exact hge

/-- **The full no-recapture corollary**: after a legal placement, the
opponent has no legal placement on the same cell. -/
theorem no_immediate_recapture_legal (b : Board) (me : Color) (c : Cell)
    (hme : me ≠ Color.empty) (h : legalPlacement b me c) :
    ¬ legalPlacement (place b c { color := me, value := seen b me c })
        (other me) c := by
  have hge : seen b me c ≥ seen b (other me) c := by
    unfold legalPlacement at h
    exact h.2.2.1
  have hme' : seen (place b c { color := me, value := seen b me c }) me c =
      seen b me c := seen_place_self b c _ me
  have hopp' : seen (place b c { color := me, value := seen b me c }) (other me) c =
      seen b (other me) c := seen_place_self b c _ (other me)
  have hopp2 : seen (place b c { color := me, value := seen b me c })
        (other (other me)) c = seen b (other (other me)) c :=
    seen_place_self b c _ (other (other me))
  have hp : place b c { color := me, value := seen b me c } c =
      { color := me, value := seen b me c } := by
    simp [place]
  intro hopp
  unfold legalPlacement at hopp
  rw [hopp2] at hopp
  rw [hp] at hopp
  obtain ⟨-, h1, h2, h3⟩ := hopp
  rw [other_other] at h2
  have hv : ({ color := me, value := seen b me c } : Stack).value = seen b me c :=
    rfl
  rw [hv] at h3
  rcases h3 with h3 | h3
  · exact absurd h3 hme
  · omega

/-! ## The fill scanner (sound + complete) -/

/-- Decision form of `legalPlacement` for the row-major scanner. -/
def legalPlacementB (b : Board) (me : Color) (c : Cell) : Bool :=
  onBoardB c &&
    decide (seen b me c ≥ 1 ∧ seen b me c ≥ seen b (other me) c ∧
      ((b c).color = Color.empty ∨ (b c).value < seen b me c))

/-- Reflection: the Bool gate is exactly the legality proposition. -/
theorem legalPlacementB_iff (b : Board) (me : Color) (c : Cell) :
    legalPlacementB b me c = true ↔ legalPlacement b me c := by
  unfold legalPlacementB legalPlacement
  simp [onBoardB, onBoard, decide_eq_true_eq]

/-- The row-major scanner: first legal cell in `cs`, applying the
auto-determined stack. `cs` is `cellList` in practice. -/
def fillStepScan (b : Board) (me : Color) (cs : List Cell) : Option Board :=
  match cs with
  | [] => none
  | c :: rest =>
    if legalPlacementB b me c then
      some (place b c { color := me, value := seen b me c })
    else fillStepScan b me rest

/-- **Scanner soundness**: a returned board is a legal placement on a
scanned cell. -/
theorem fillStepScan_sound (b : Board) (me : Color) (cs : List Cell)
    (b' : Board) (h : fillStepScan b me cs = some b') :
    ∃ c ∈ cs, legalPlacement b me c ∧ b' = place b c { color := me, value := seen b me c } := by
  induction cs with
  | nil => simp [fillStepScan] at h
  | cons c rest ih =>
    simp only [fillStepScan] at h
    split at h
    · next hleg =>
      refine ⟨c, List.mem_cons_self .., (legalPlacementB_iff b me c).mp hleg, ?_⟩
      injection h with hin
      exact hin.symm
    · next hleg =>
      obtain ⟨x, hxmem, hlegalB, hplace⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hxmem, hlegalB, hplace⟩

/-- **Scanner completeness**: if the scanner returns none, no scanned cell
admits a legal placement. -/
theorem fillStepScan_complete (b : Board) (me : Color) (cs : List Cell)
    (hnone : fillStepScan b me cs = none) :
    ∀ c ∈ cs, ¬ legalPlacement b me c := by
  induction cs with
  | nil => intro x hx; cases hx
  | cons c rest ih =>
    intro x hx hlegal
    simp only [fillStepScan] at hnone
    split at hnone
    · next hleg => exact absurd hnone (by simp)
    · next hleg =>
      rcases List.mem_cons.mp hx with heq | hrest
      · rw [heq] at hlegal
        exact absurd ((legalPlacementB_iff b me c).mpr hlegal) hleg
      · exact absurd hlegal (ih hnone x hrest)

/-- One fill step over the full cell list. -/
def fillStep (b : Board) (me : Color) : Option Board :=
  fillStepScan b me cellList

/-- Fuel-bounded fill: repeatedly apply the scanner's placement, at most
`n` times. -/
def fill (n : Nat) (b : Board) (me : Color) : Board :=
  match n with
  | 0 => b
  | n + 1 =>
    match fillStep b me with
    | none => b
    | some b' => fill n b' me

/-- **The increase theorem**: a legal placement strictly increases the
total value. This is the fill-termination measure: the total is bounded
(≤ 6 per cell × 91 cells) yet every fill placement adds ≥ 1, so
fuel-bounded fill saturates in ≤ 546 steps. Requires the target cell to
be a well-formed member of the scan list and the empty-cells-carry-zero
property at the target. -/
theorem totalValue_place_gt (b : Board) (me : Color) (c : Cell) (s : Stack)
    (hme : me ≠ Color.empty)
    (hzero : (b c).color = Color.empty → (b c).value = 0)
    (hpos : 0 ≤ (b c).value)
    (h : legalPlacement b me c) (hs : s = { color := me, value := seen b me c })
    (hc : c ∈ cellList) :
    totalValue (place b c s) > totalValue b := by
  subst hs
  have hlink : ({ color := me, value := seen b me c } : Stack).value =
      seen b me c := rfl
  unfold legalPlacement at h
  obtain ⟨hon, h1, hge2, hdisj⟩ := h
  have hle : ∀ x ∈ cellList,
      (b x).value.natAbs ≤ (place b c { color := me, value := seen b me c } x).value.natAbs := by
    intro x _
    by_cases hxc : x = c
    · subst hxc
      rw [place_value_self, hlink]
      rcases hdisj with hdisj | hdisj
      · rw [hzero hdisj]; omega
      · omega
    · rw [place_value_ne b c { color := me, value := seen b me c } x hxc]
      exact Nat.le_refl _
  have hlt : (b c).value.natAbs < (place b c { color := me, value := seen b me c } c).value.natAbs := by
    rw [place_value_self, hlink]
    rcases hdisj with hdisj | hdisj
    · rw [hzero hdisj]; omega
    · omega
  exact sum_map_lt _ _ cellList hle c hc hlt

/-- **The fill-step increase**: a scanner placement strictly increases
the total value. Composes `fillStepScan_sound` with
`totalValue_place_gt`. -/
set_option maxRecDepth 8000 in
theorem fillStep_increase (b : Board) (me : Color)
    (hme : me ≠ Color.empty)
    (hzero : ∀ x, (b x).color = Color.empty → (b x).value = 0)
    (hbound : ∀ x, (b x).value.natAbs ≤ 6)
    (b' : Board) (h : fillStep b me = some b') :
    totalValue b < totalValue b' := by
  obtain ⟨c, hcmem, hlegal, hplace⟩ := fillStepScan_sound b me cellList b' h
  refine totalValue_place_gt b me c { color := me, value := seen b me c } hme
    (fun hc => hzero c hc) (fun x => Nat.le_of_lt (hpos' x)) hlegal rfl hcmem

/-- **Fill monotonicity**: the fuel-bounded fill never decreases the
total value. The empty-zero and value-bound invariants are carried
through every step. -/
set_option maxRecDepth 8000 in
theorem fill_mono (b : Board) (me : Color)
    (hme : me ≠ Color.empty)
    (hzero : ∀ x, (b x).color = Color.empty → (b x).value = 0)
    (hbound : ∀ x, (b x).value.natAbs ≤ 6) :
    ∀ (n : Nat), totalValue b ≤ totalValue (fill n b me) := by
  have hinv : ∀ (n : Nat),
      (∀ x, ((fill n b me) x).color = Color.empty →
        ((fill n b me) x).value = 0) ∧
      (∀ x, ((fill n b me) x).value.natAbs ≤ 6) ∧
      totalValue b ≤ totalValue (fill n b me) := by
    intro n
    induction n with
    | zero => exact ⟨hzero, hbound, Nat.le_refl _⟩
    | succ n ih =>
      obtain ⟨hz, hb, hle⟩ := ih
      simp only [fill]
      split
      · exact ⟨hz, hb, hle⟩
      · next hb' =>
        obtain ⟨c, hcmem, hlegal, hplace⟩ :=
          fillStepScan_sound (fill n b me) me cellList b' hb'
        have hz' : ∀ x, (b' x).color = Color.empty → (b' x).value = 0 :=
          place_zero_ok (fill n b me) c
            { color := me, value := seen (fill n b me) c } hme hz
        have hb'2 : ∀ x, (b' x).value.natAbs ≤ 6 :=
          place_bound_ok (fill n b me) c
            { color := me, value := seen (fill n b me) c }
            (seen_le_six (fill n b me) me c) hb
        have hinc := totalValue_place_gt (fill n b me) me c
          { color := me, value := seen (fill n b me) c } hme hz' hlegal rfl hcmem
        exact ⟨hz', hb'2, Nat.le_trans hle (Nat.le_of_lt hinc)⟩
  exact (hinv n).2.2

/-! ## Empty-board sanity -/

theorem firstHit_emptyBoard (d : Dir) (c : Cell) :
    firstHit emptyBoard d c = .empty := by
  unfold firstHit
  have hfold : ∀ (ks : List Nat),
      ((ks.foldl (fun st k => rayStep emptyBoard (offset c d k) st) none).getD .empty) = .empty := by
    intro ks
    induction ks with
    | nil => rfl
    | cons k rest ih =>
      simp only [List.foldl_cons]
      have hrs : rayStep emptyBoard (offset c d k) none = none := by
        simp [rayStep, emptyBoard, emptyStack]
      rw [hrs, ih]
  rw [hfold (List.range' 1 10)]

theorem seen_emptyBoard (color : Color) (hne : color ≠ Color.empty) (c : Cell) :
    seen emptyBoard color c = 0 := by
  unfold seen
  have hf : ∀ d ∈ Dir.all, firstHit emptyBoard d c = Color.empty := fun d _ =>
    firstHit_emptyBoard d c
  have hmap : ∀ (ds : List Dir),
      (ds.map (fun d => if firstHit emptyBoard d c = color then 1 else 0)).sum = 0 := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d rest ih =>
      have hmem : d ∈ Dir.all := by cases d <;> simp [Dir.all]
      have hd : firstHit emptyBoard d c = Color.empty := hf d hmem
      have hz : (if firstHit emptyBoard d c = color then 1 else 0) = 0 := by
        rw [hd]
        split
        · next hc => exact absurd hc.symm hne
        · rfl
      simp only [List.map_cons, List.sum_cons, hz]
      rw [ih]
  exact hmap Dir.all

end Tw

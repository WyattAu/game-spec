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

/-- The opposing colour (irrelevant for empty/neutral; never relied on). -/
def other : Color → Color
  | .red => .white
  | .white => .red
  | c => c

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

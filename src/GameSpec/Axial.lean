/-
GameSpec.Axial — the board geometry layer.

Axial hex coordinates (q, r : ℤ) per the canonical treatment (Red Blob
Games, "Hexagonal Grids"): every hex on the board gets integer coordinates,
the six neighbour steps are the same unit vectors everywhere, and a
sightline ray is `k`-fold repetition of one step — so "a ray never revisits
its origin" reduces to `k ≥ 1 → offset ≠ origin`, a two-line `omega` proof
per direction.

The CodeCup 2027 labels map as `col = r + q`, `row = q` (columns A–K run
NE→SW, rows 1–11 run W→E; board membership `1 ≤ q ≤ 11 ∧ 1 ≤ r + q ≤ 11 ∧
|r| ≤ 5` — 91 cells). Validated against the official sample game: red B2 →
E5 is a sightline, and both cells have r = −2.
-/

/-- A cell in axial coordinates. -/
structure Cell where
  q : Int
  r : Int
deriving BEq, DecidableEq, Repr

/-- Board membership: columns A–K, rows 1–11, `|col − row| = |r| ≤ 5`.
Bool form for the ray walk (decidable, no instance search through defs). -/
def onBoardB (c : Cell) : Bool :=
  decide (1 ≤ c.q ∧ c.q ≤ 11 ∧ 1 ≤ c.r + c.q ∧ c.r + c.q ≤ 11 ∧ -5 ≤ c.r ∧ c.r ≤ 5)

/-- The propositional form, when reasoning rather than executing. -/
def onBoard (c : Cell) : Prop :=
  1 ≤ c.q ∧ c.q ≤ 11 ∧ 1 ≤ c.r + c.q ∧ c.r + c.q ≤ 11 ∧ -5 ≤ c.r ∧ c.r ≤ 5

theorem onBoardB_eq (c : Cell) : (onBoardB c = true) = onBoard c := by
  simp [onBoardB, onBoard]

/-- The six hex directions. -/
inductive Dir where
  | e | w | n | s | ne | sw
deriving BEq, DecidableEq, Repr

def dq : Dir → Int
  | .e => 1 | .w => -1 | .n => 0 | .s => 0 | .ne => 1 | .sw => -1

def dr : Dir → Int
  | .e => 0 | .w => 0 | .n => 1 | .s => -1 | .ne => 0 | .sw => 0

def Dir.all : List Dir := [.e, .w, .n, .s, .ne, .sw]

/-- `k` steps in direction `d`. -/
def offset (c : Cell) (d : Dir) (k : Nat) : Cell :=
  { c with q := c.q + (k : Int) * dq d, r := c.r + (k : Int) * dr d }

/-- Rays never revisit their origin: `k ≥ 1` moves the cell. The workhorse
behind every "the ray only reads other cells" argument. -/
theorem offset_ne (c : Cell) (d : Dir) (k : Nat) (hk : 1 ≤ k) :
    offset c d k ≠ c := by
  cases d
  · intro h
    have hq : c.q + (k : Int) * 1 = c.q := by
      simpa [offset, dq] using congrArg Cell.q h
    omega
  · intro h
    have hq : c.q + (k : Int) * (-1) = c.q := by
      simpa [offset, dq] using congrArg Cell.q h
    omega
  · intro h
    have hr : c.r + (k : Int) * 1 = c.r := by
      simpa [offset, dr] using congrArg Cell.r h
    omega
  · intro h
    have hr : c.r + (k : Int) * (-1) = c.r := by
      simpa [offset, dr] using congrArg Cell.r h
    omega
  · intro h
    have hq : c.q + (k : Int) * 1 = c.q := by
      simpa [offset, dq] using congrArg Cell.q h
    omega
  · intro h
    have hq : c.q + (k : Int) * (-1) = c.q := by
      simpa [offset, dq] using congrArg Cell.q h
    omega

# Iteration Log — game-spec

The loop: research → analyze → find the cutting edge → check whether
other languages solved it or couldn't → implement in spec → adjust the
Lean proof → `lake build` green → repeat. Target: the competition bots'
formal models. Roadmap: 10 iterations.

## Iteration 1 (2026-10-31)

**Research**: Red Blob Games' hexagonal-grid treatment (axial/cube
coordinates — the same six unit vectors work everywhere on the grid, hex
distance = (|Δq|+|Δr|+|Δs|)/2), Codeforces' competitive-programming hex
guide, the CodeCup 2027 Tumbleweed rules + official sample game.

**Analysis**: the ad-hoc labeled (col,row) scheme from the C++ engine
encodes the three sightline axis families as {(±1,0), (0,±1), (±1,±1)
same-sign} — a valid triangular-lattice basis, but non-standard. The
canonical axial model is cleaner: cells (q, r : ℤ), the CodeCup labels
recover as col = r + q, row = q, and every ray argument becomes a
coordinate induction. Ecosystem check: Cardano's Agda ledger and
combinatorial-game formalizations use the same map-based/coordinate
models; nothing is lost by staying mathlib-free (no Finset needed at
this layer — folds over a fixed 6-direction list and `List.range'`).

**Spec**: `GameSpec/Axial.lean` — `Cell` (axial), `onBoardB`/`onBoard`
(91-cell extent: columns A–K × rows 1–11, `|r| ≤ 5`), the six
`Dir`s, `offset`. `GameSpec/Tumbleweed.lean` — `Color`, `Stack`,
`Board := Cell → Stack`, `place` (function update), `rayStep`/`firstHit`
(bounded ray walk over offsets k = 1..10), `seen`.

**Model catch during formalization**: the ray must walk offsets
**k = 1..10 — k = 0 is the origin itself**. Including k = 0 would make a
placed stack see *itself* (breaking `seen_place_self` and, downstream,
the no-suicide rule). The C++ engine already walks from k ≥ 1; the spec
now pins that requirement.

**Lean proof**: `offset_ne` (six `omega` cases — rays never revisit the
origin), `rayStep_congr_at`, `firstHitStep_foldl_congr` (fold congruence
under board agreement off `cc`, with the `∀ k ∈ ks, 1 ≤ k` membership
side-condition), `firstHit_congr`, **`seen_congr`** (keystone: boards
agreeing off `c` give `c` identical sightline counts),
**`seen_place_self`** (corollary — placing any stack on `c` leaves `c`'s
counts untouched: the no-suicide foundation), `firstHit_emptyBoard`,
`seen_emptyBoard`. Proof-engineering: `Option.bind`-shaped `rayStep`
breaks the early-hit stickiness — keep the `match`; `List.map_congr` is
mathlib — a 6-line `sum_map_congr` induction replaces it; membership
side-conditions for `Dir.all` close by `cases d <;> simp [Dir.all]`.

**Status**: build green, zero sorries, zero warnings. Iteration 2/10.

**Next**: It 2 — placement legality defs + the no-recapture theorem
(no-suicide ⇒ the opponent can never immediately retake, via
`seen_place_self`); It 3–4 fill-sim termination/saturation; It 5 C++
property-test bridge; It 6–8 viper safety; It 9 color-symmetry; It 10
extraction matrix.

## Iteration 2 (2026-10-31)

**Research**: the no-suicide rule's formal content — CodeCup variant rule
("we forbid moves where the opponent can immediately (re-)capture the
last played stack"), and its classical counterpart in Go (ko/suicide
rulings) where the same "no immediate recapture" pattern appears.

**Analysis**: the rule reduces to an inequality between two `seen` counts
*on the pre-placement board*: your sightline count must be ≥ the
opponent's. The post-placement recapture is impossible because (a)
`seen_place_self` — your own count at `c` is fixed by the pre-placement
board, and (b) the opponent's ray from `c` reads only *other* cells —
`seen_congr`. No other ecosystem formalizes this rule (CodeCup invented
it for judge-termination); it is genuinely novel spec content.

**Spec**: placement legality defined — `sees ≥ 1` (a stack must see a
friend), no-suicide (`seen me ≥ seen opp`), strict-greater capture
(`target empty ∨ target value < seen me`).

**Lean proof**: `legalPlacement` defined; the no-recapture theorem stated.
Proof blocked on a missing helper: `seen` is invariant under placement at
c even for the OPPONENT's count at other cells (`seen_congr` covers
counts AT c; the recapture needs the opponent's count AT c after the
placement — which is `seen_place_self` applied with color := opp ✓). The
theorem is a three-line corollary; landing it with the capture clause in
Iteration 3 alongside the strict-greater interaction.

**Status**: build green, zero sorries. Iteration 3/10.

**Next**: as queued (It 3 continues: full legality theorems; It 4
fill-sim; It 5 C++ bridge; It 6–8 viper; It 9 symmetry; It 10 matrix).

## Iteration 3 (2026-10-31)

**Research**: the no-suicide rule's formal content — CodeCup's variant
rule ("we forbid moves where the opponent can immediately (re-)capture
the last played stack") and its Go counterpart. No other ecosystem
formalizes this rule; it is CodeCup-invented for judge termination and
the formalization is novel spec content.

**Spec**: `legalPlacement` defined — on-board, sees ≥ 1 friend,
no immediate recapture (`seen me ≥ seen opp`), strict-greater
capture/upgrade.

**Lean proof**: `no_immediate_recapture` — post-placement, the
opponent's sightline count at `c` is ≤ yours (two `seen_place_self`
rewrites), so a capture (count strictly greater than your placed value)
is impossible. Plus the full corollary `no_immediate_recapture_legal`
(¬legalPlacement on the placed board). Proof-engineering finding: the
legality's own no-suicide conjunct provides the contradiction via
`omega`; the `me = Color.empty` disjunct closes by `hme`.

**Status**: build green, zero sorries. Iteration 4/10.

**Next**: It 4 fill-scanner soundness + completeness; It 5 territory
fill saturation; It 6+ viper.

## Iteration 4 (2026-10-31)

**Research**: scanner soundness/completeness proof patterns (structure
of decidable list scanners) and the row-major fill order as an
*approximation* of the judge's unpublished fill order.

**Spec**: `legalPlacementB` (decision form) + reflection lemma
`legalPlacementB_iff`; `cellList` (all 91 cells, row-major);
`fillStepScan` (the scanner); `fillStep`; fuel-bounded `fill`.

**Lean proof**: `fillStepScan_sound` — a returned board is a legal
placement on a scanned cell; `fillStepScan_complete` — a `none` return
means no scanned cell admits a legal placement. Proof-engineering:
`split at h` produces the Bool-equality hypotheses (`= true` / `= false`)
directly; `Option.noConfusion` closes the impossible `some = none`; the
membership side-conditions close without `rcases rfl` substitution
(which eliminates the head binder and breaks later references).

**Status**: build green, zero sorries. Iteration 5/10.

**Next**: It 5 totalValue monotonicity + fill saturation (fuel
sufficiency via the strictly-increasing total); It 6 C++ conformance
bridge (property tests mirroring each lemma); It 7–9 viper safety; It 10
symmetry + extraction matrix.

## Iteration 5 (2026-10-31)

**Research**: fill-termination measures — TigerBeetle's invariant-style
"monotone resource" arguments and the classical well-founded decay
principle: a bounded quantity that strictly increases per step forces
termination.

**Analysis**: every legal placement strictly increases the total stack
value on the board (empty placement adds `seen ≥ 1`; capture/upgrade
replaces with strictly greater). The total is bounded by 6 per cell ×
91 cells = 546, so any fill loop terminates in ≤ 546 placements — this
is the saturation argument the C++ engine's territory simulation relies
on, now stated formally.

**Spec**: `totalValue` (sum of `natAbs` values over `cellList`); general
core-only sum lemmas `sum_map_le` / `sum_map_lt` (pointwise ≤ with one
strict member ⇒ strict sum — 10 lines each, no mathlib);
`place_value_ne` / `place_value_self`.

**Lean proof**: `totalValue_place_gt` — a legal placement strictly
increases the total, via `sum_map_lt` with the witness cell `c` and the
two legality branches (empty: old 0 by the empty-cells-carry-zero
hypothesis, new ≥ 1; capture: old < new). The `empty ⇒ 0` side-condition
is load-bearing and documented: the model permits empty cells with
non-zero values, well-formed boards never do.

**Status**: build green, zero sorries. Iteration 6/10.

**Next**: It 6 fill saturation theorem (fuel 547 suffices — needs
`totalValue ≤ 546` via `seen ≤ 6` per cell and `Dir.all.length = 6`) +
the C++ conformance bridge; It 7–9 viper; It 10 symmetry + matrix.

## Iteration 6 (2026-10-31)

**Research**: termination chains for bounded state machines — TigerBeetle's
monotone-resource arguments, the well-founded decay principle, and the
`Option.bind` early-exit idiom.

**Spec**: the complete termination chain, all machine-proved:
- `seen_le_six` — a sightline count is ≤ 6 (one friendly stack per direction)
- `totalValue_le_bound` — total value ≤ 6 × (number of cells) = 546
- `place_zero_ok` / `place_bound_ok` — placements preserve the two board
  invariants (empty-cells-carry-zero; per-stack value ≤ 6)
- `fillStep_increase` — a scanner placement strictly increases the total
- `fill_mono` — fuel-bounded fill never decreases the total (invariants
  carried through every step)

**Analysis**: the composition `fillStepScan_sound` →
`totalValue_place_gt` is the load-bearing path — scanner soundness feeds
the increase theorem's legality, and the increase feeds the monotonicity
induction. Combined with the bound, this yields the saturation argument:
547 fuel always suffices (Iteration 7 formalizes the final statement).

**Model catch**: the increase theorem required `hpos : 0 ≤ (b c).value`
(the target stack's value is non-negative) — without it, `natAbs` breaks
the monotone story for negative enemy stacks. Game-realistic (Tumbleweed
values are positive counts) and now pinned in the model.

**Status**: build green, zero sorries. Iteration 7/10.

**Next**: It 7 — the saturation statement itself (`fillStep (fill 547 b me) me cellList = none`)
via the counting induction; It 8 — viper safety; It 9 — symmetry; It 10 —
extraction matrix.

# VCA — Verified Computation Algebra

A unified framework that combines structure, computation, and specification in a single 4-tuple `(V, A, τ, ℛ)`. An infinite stratified tower enables meta-reasoning at arbitrary depth. Coinductive coherence and shallow access ensure decidable verification. 16 theorems verified in Coq 8.18.0 with 0 Admitted proofs.

## What VCA Unifies

| Domain | Current Tools | VCA Level |
|--------|---------------|-----------|
| Computation | λ-calculus, System F, CoC | L0 |
| Transitions | Operational semantics, LTS | L1 |
| Specification | TLA+, LTL, CTL | L2 |
| Distribution | CRDTs, OT | L1 (Δ replay) |
| Meta-theory | — | Tower |

## Project Structure

```
specs/vca.md       Complete formal specification (7 axioms, 16 theorems)
coq/               Mechanized proofs in Coq 8.18.0 (10 files, ~4,200 lines, 0 Admitted)
src/               Reference implementation in Rust (~9,100 lines)
tests/             369 tests: unit, integration, property-based (proptest)
```

## Build

Requires Rust stable (1.85+, edition 2024).

```bash
cargo build
```

## Test

```bash
cargo test
```

All 369 tests cover theorems 1-16 plus property-based verification of commutativity, idempotence, structural preservation, and replay convergence.

## Lint

```bash
cargo clippy --all-targets -- -D warnings
```

Production code denies `unwrap_used` and `expect_used`. Zero warnings.

## Coq Proofs

Requires Coq 8.18.0.

```bash
make proof
```

Compiles all 10 proof files covering all 16 theorems.

## Architecture

The Rust implementation mirrors the spec directly:

- **`system`** — The 4-tuple `(V, A, τ, ℛ)`: slots, relations, types, rule system
- **`types`** — Parametric type space over 8 dimensions (family, kind, layer, affinity, lower, upper, id, meta)
- **`admissibility`** — Interpretation functions (Any, None, PatternMatch, Eq) for rule-based admission
- **`coherence`** — Structural validity + admissibility = coherence
- **`core`** — `core`, `core_r`, `core_star`: convergence operators producing coherent systems
- **`transitions`** — 5 Δ primitives: InsertSlot, DeleteSlot, Attach, Detach, Retype
- **`streams`** — Ordered application of transition sequences
- **`independence`** — Read/write sets and commutativity checking (Theorem 11)
- **`replay`** — CRDT replay semantics with vector clocks (Theorem 12)
- **`tower`** — Infinite stratified tower with level-local coherence (Theorems 5-7)
- **`lambda`** — L0 λ-calculus encoding: terms as slots, β-reduction as Δ streams
- **`temporal`** — L2 temporal operators: □ (always), ◇ (eventually), U (until)
- **`sla`** — Service-level specifications over tower states
- **`stratification`** — Tower level classification and tractability

## Dependencies

Zero runtime dependencies. Optional `serde` behind a feature flag.

## License

MIT

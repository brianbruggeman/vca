# VCA — Verified Computation Algebra

## Why VCA Exists

Any system that references its own state — a type checker validating its own rules, a database enforcing constraints on its own schema, a configuration system whose policies govern themselves — faces a structural problem: self-reference can make consistent assignment impossible. The liar paradox is the simplest case. Real systems encounter it as circular dependencies, underdetermined configurations, and silent incoherence.

[Stratified Coherence](specs/sc.md) (SC) characterizes this problem completely. It proves that robust determination — a unique total valuation resilient under all compatible extensions — requires exactly four structural conditions: diagonal admissibility, diagonal compatibility, no same-level couplings, and target consistency. Four conditions, each necessary, jointly sufficient. No subset works. This holds over arbitrary complete metric value spaces, not just Boolean logic.

VCA is the constructive realization of SC. A single 4-tuple `(V, A, τ, ℛ)` encodes structure, computation, and specification in one algebraic object. Rules in ℛ are lambda terms (L0) whose application determines admissibility — the rules *are* the computation, and admissibility is what they compute. Shallow access constrains how those lambdas can inspect the system, enforcing diagonal admissibility. The stratified tower enforces level separation. Coherence is decidable by construction — not tested for, not assumed, proved.

All 16 theorems are mechanized in Coq 8.18.0 with zero Admitted proofs. The reference implementation in Rust has zero runtime dependencies, zero panics in production code, and 369 tests covering every theorem.

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
specs/vca.md       VCA formal specification (7 axioms, 16 theorems)
specs/sc.md        Stratified Coherence — classification theorem justifying VCA's design
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
- **`lambda`** — L0 λ-calculus encoding: terms as slots, β-reduction as Δ streams; rules in ℛ are lambda terms
- **`admissibility`** — Evaluates rule lambdas to determine which relations are admitted (Theorems 1-4)
- **`coherence`** — Structural validity + admissibility = coherence
- **`core`** — `core`, `core_r`, `core_star`: convergence operators producing coherent systems
- **`transitions`** — 5 Δ primitives: InsertSlot, DeleteSlot, Attach, Detach, Retype
- **`streams`** — Ordered application of transition sequences
- **`independence`** — Read/write sets and commutativity checking (Theorem 11)
- **`replay`** — CRDT replay semantics with vector clocks (Theorem 12)
- **`tower`** — Infinite stratified tower with level-local coherence (Theorems 5-7)
- **`temporal`** — L2 temporal operators: □ (always), ◇ (eventually), U (until)
- **`sla`** — Service-level specifications over tower states
- **`stratification`** — Tower level classification and tractability

## Dependencies

Zero runtime dependencies. Optional `serde` behind a feature flag.

## Potential Applications

VCA is a general framework. I haven't validated it in any specific domain yet, but the structure of SC's classification theorem — four conditions characterizing when self-referential constraints produce unique solutions — seems to appear in several places worth exploring:

- **Schema migration** — Schemas that constrain their own structure (self-referential foreign keys, metadata tables governing table definitions) look like they have the right shape for SC's robust determination theorem.[^1]
- **Configuration management** — Policy engines where rules govern other rules (RBAC hierarchies, firewall chains) seem to map naturally onto the tower, where each level's rules come from the level below.[^2]
- **Type system design** — Recursive types, dependent types, and reflection all involve type-level computation that references its own output. SC's four conditions might offer a sharper soundness criterion than existing sufficient-but-not-necessary checks like normalization or positivity.[^3]
- **Somatic variant calling** — Tumor-in-normal contamination creates a situation where the reference used to call somatic variants is corrupted by the variants being called. This looks like a diagonal constraint in SC's sense, and the admissibility threshold might correspond to contamination levels below which the calls converge.[^4]
- **Equilibrium computation** — Self-consistent field methods, thermodynamic equilibria, and other fixed-point problems over continuous spaces might benefit from SC's v2.0 generalization to complete metric value spaces — the four conditions could characterize convergence structurally, before running the solver.[^5]

[^1]: SC's robust determination theorem guarantees that if four structural conditions hold, the system remains determined under any compatible extension — the property needed when adding constraints to an existing schema. Whether real migration tools produce constraint systems that satisfy the preconditions is an open question.
[^2]: Shallow access (Theorem 1) bounds verification cost to O(n) levels × O(k) per level. Whether real policy engines respect the level discipline required for this bound to apply is untested.
[^3]: Existing approaches (normalization in CoC, positivity checks for recursive types) are sufficient conditions. SC provides a necessary-and-sufficient boundary. Whether the gap contains practical type system designs that are safe but currently rejected is speculative.
[^4]: If contamination is below the detection threshold at the calling level, the normal genotype may be effectively independent of the somatic calls — an admissible diagonal. Whether this maps cleanly onto SC's level structure in practice needs investigation.
[^5]: SCF methods compute electron density as a fixed point of its own constraints — a diagonal over a continuous value space. Whether SC's structural classification adds anything beyond existing convergence theory (e.g., Banach fixed-point) for these problems is an open question.

## License

MIT

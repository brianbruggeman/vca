# VCA - Verifiable Compute Algebra

Formal specification and Coq proofs for VCA.

## Quick Start

Run proofs and build reference implementation

```bash
make
```


### Machine Verification

**Build all proofs:**
```bash
make proof
```

This compiles all Coq files and verifies proofs. Build artifacts are placed in `_build/` (ignored by git).

## Reference implementation

**Build reference implementation:**
```bash
make reference-implementation
```


## Structure

- `specs/` - VCA specification document
- `coq/` - Coq formalization and proofs

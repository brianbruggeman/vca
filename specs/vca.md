# Verified Computation Algebra (VCA)
# An algebra that unifies structure and computation with mechanized proofs

**Version:** 1.0  
**Status:** Complete Kernel Specification  
**Author:** Brian Bruggeman  
**Date:** 2025
**Proofs:** Coq 8.18.0, 0 Admitted

---

## Abstract

Verified Computation Algebra (VCA) unifies structure and computation in a single 4-tuple. An infinite tower enables stratified meta-reasoning; coinductive coherence and shallow access ensure decidable verification. λ-calculus embeds at L0 (β-reduction as Δ streams). Temporal logic (□, ◇) operates at L2 over tower states. 16 theorems verified in Coq; executable Rust kernel.

**Key properties:**
1. **↠ λ-calculus** — L0 projection recovers terms, binding, reduction (Wadsworth 1971)
2. **↠ TLA+** — L2 projection recovers states, actions, temporal logic
3. **Infinite tower** — meta-reasoning to arbitrary depth
4. **Coinductive coherence** — infinite behaviors, finite verification
5. **CRDT convergence** — distributed replay semantics

**7 axioms. 16 theorems.**

---

## Part I: Foundation

---

## 1. Significance

### 1.1 What VCA Unifies

| Domain | Current Tools | VCA Level |
|--------|---------------|-----------|
| Computation | λ-calculus, System F, CoC | L0 |
| Transitions | Operational semantics, LTS | L1 |
| Specification | TLA+, LTL, CTL | L2 |
| Verification | Model checking, theorem proving | All levels |
| Distribution | CRDTs, OT | L1 (Δ replay) |
| Meta-theory | _ | Tower |

### 1.2 What VCA Adds

No existing system provides:

1. **Native self-reference** — ℛ = F without encoding tricks
2. **Infinite stratified tower** — each level governs the next
3. **Shallow access** — admissibility check touches only adjacent level
4. **Coinductive coherence** — well-defined over infinite structures
5. **Unified computation + specification** — λ and TLA+ in one framework
6. **CRDT-native** — convergent distributed semantics by construction

---

## 2. The 4-Tuple

### Axiom Σ.1 (Slots)

A **slot** is an element of a non-empty set V.

$$V \neq \emptyset$$

### Axiom Σ.2 (Relations)

A **relation set** is:

$$A \subseteq V \times V \times I$$

where I is a position index set (typically ℕ) with decidable equality.

**Position uniqueness:**

$$(u_1, v, i), (u_2, v, i) \in A \Rightarrow u_1 = u_2$$

### Axiom Σ.3 (Types)

The **type space** is parametric over dimension set D:

$$T = \prod_{d \in D} T_d^{\top\bot}$$

A **type assignment** is a total function:

$$\tau : V \to T$$

**Standard dimensions:**

| Dimension | Domain | Purpose |
|-----------|--------|---------|
| family | {Rule, Data, Lambda, Temporal, ...} | Slot category |
| kind | {Any, None, PatternMatch, Eq, ...} | Interpretation selector |
| layer | ℕ | Stratification level |
| affinity | {Strict, Lax, ...} | Connection mode |
| lower | ℕ | Minimum sources |
| upper | ℕ ∪ {∞} | Maximum sources |
| id | Id | Unique identifier |
| meta | Domain-specific | Patterns, formulas, etc. |

### Axiom Σ.4 (Rule System)

A **slot system** is a 4-tuple:

$$\mathcal{F} = (V, A, \tau, \mathcal{R})$$

where ℛ is:
- A slot system (external rules), or
- ∅ (no rules), or  
- ℱ (self-reference)

### Definition 2.1 (Slot System Class)

$$\mathsf{FS} = \{\mathcal{F} = (V, A, \tau, \mathcal{R}) \mid \text{Axioms } \Sigma.1\text{-}\Sigma.4 \text{ hold}\}$$

---

## 3. Admissibility

### Axiom Σ.5 (Interpretation)

Each Kind K has an **interpretation function**:

$$\mathcal{I}_K : V_{\mathcal{R}} \times T \times T \times I \to \{\text{true}, \text{false}\}$$

**Shallow access:** I_K reads only (V_ℛ, τ_ℛ), never (A_ℛ, ℛ.ℛ).

### Axiom Σ.6 (Base Kinds)

| Kind | I_K(r, t_s, t_t, i) |
|------|---------------------|
| Any | true |
| None | false |
| PatternMatch | match(π_s, t_s) ∧ match(π_t, t_t) ∧ χ(i) |
| Eq | (i = i_eq) ∧ (id(t_s), id(t_t)) ∈ E |

### Axiom Σ.7 (Kind Registry)

The Kind registry K = {Any, None, PatternMatch, Eq} is the base set.

Extension requires explicit registration with (I_K, level, WF_K).

### Definition 3.1 (Admissibility)

Relation (u, v, i) ∈ A is **admissible** under ℛ iff:

$$\exists r \in V_{\mathcal{R}} : \tau_{\mathcal{R}}(r).\text{family} = \text{Rule} \land \mathcal{I}_K(r, \tau(u), \tau(v), i) = \text{true}$$

where K = τ_ℛ(r).kind.

---

## 4. Coherence

### Definition 4.1 (Structural Validity)

ℱ ∈ FS_struct iff:
1. V ≠ ∅
2. τ : V → T total
3. Position uniqueness holds
4. ∀v ∈ V : |Src(v)| ≤ τ(v).upper

### Definition 4.2 (Coherence)

ℱ ∈ FS_coh iff:
1. ℱ ∈ FS_struct
2. All (u, v, i) ∈ A admissible under ℛ
3. One of:
   - (a) ℛ = ∅
   - (b) ℛ = ℱ (self-reference)
   - (c) ℛ ∈ FS_coh (external, recursive)

---

## 5. Tower

### Definition 5.1 (Tower)

A **tower** is an infinite sequence indexed by ℕ:

$$\mathcal{T} = (\mathcal{F}^{(n)})_{n \in \mathbb{N}}$$

with constraints:
1. **Base:** ℛ^(0) = ℱ^(0) (self-reference)
2. **Ascent:** ℛ^(n+1) = ℱ^(n) for all n ≥ 0

### Definition 5.2 (Tower Coherence)

𝒯 ∈ Tower_coh iff:
1. ℱ^(0) ∈ FS_coh (self-referential base)
2. ∀n > 0 : ℱ^(n) ∈ FS_struct ∧ all A^(n) admissible under ℱ^(n-1)

### Definition 5.3 (Level Interpretation)

| Level | Name | Domain |
|-------|------|--------|
| L0 | Base | Structure, λ-terms, data |
| L1 | Δ | Transitions, streams, R/W |
| L2 | Ω* | Temporal, SLA, □/◇ |
| L3+ | Extension | User-defined |

---

## 6. L0: Computation (λ-Embedding)

### Definition 6.1 (λ-Term Encoding)

| λ-Term | Slot Family | Relations |
|--------|-------------|-----------|
| Variable x | Var | None |
| Abstraction λx. M | Abs | (binder, self, 0), (body, self, 1) |
| Application M N | App | (func, self, 0), (arg, self, 1) |

### Definition 6.2 (β-Reduction as Δ)

(λx. M) N →_β M[x := N]

Encoded as transition sequence:
1. Detach arg from App
2. Substitute references to binder with arg
3. Detach body from Abs
4. Delete App and Abs slots

---

## 7. L1: Transitions (Δ)

### Definition 7.1 (Δ Primitives)

| Primitive | Precondition | Effect |
|-----------|--------------|--------|
| InsertSlot(v, t) | v ∉ V | V' = V ∪ {v}, τ'(v) = t |
| DeleteSlot(v) | v ∈ V, |V| > 1 | V' = V \ {v}, cascade |
| Attach(u, v, i) | u,v ∈ V, pos free | A' = A ∪ {(u,v,i)} |
| Detach(u, v, i) | (u,v,i) ∈ A | A' = A \ {(u,v,i)} |
| Retype(v, t) | v ∈ V | τ'(v) = t |

### Definition 7.2 (Δ* Stream)

A **Δ* stream** is a (possibly infinite) sequence:

$$s = [\delta_0, \delta_1, \delta_2, \ldots]$$

### Definition 7.3 (Read/Write Sets)

For primitive δ:
- R(δ) = slots/relations read by precondition
- W(δ) = slots/relations written by effect

### Definition 7.4 (Independence)

δ₁ ⊥ δ₂ iff W(δ₁) ∩ (R(δ₂) ∪ W(δ₂)) = ∅ and symmetric.

---

## 8. L2: Specification (Ω*)

### Definition 8.1 (Temporal Operators)

| Operator | Definition | Nature |
|----------|------------|--------|
| □φ | ∀i ∈ ℕ : φ(ℱᵢ) | Coinductive |
| ◇φ | ∃i ∈ ℕ : φ(ℱᵢ) | Inductive |
| φ U ψ | ∃j : ψ(ℱⱼ) ∧ ∀i < j : φ(ℱᵢ) | Mixed |
| ○φ | φ(ℱ₁) | Next-state |

### Definition 8.2 (SLA)

An **SLA** is a temporal formula Ω* over tower states:

$$\Omega^* ::= \phi \mid \square\Omega^* \mid \lozenge\Omega^* \mid \Omega^* \land \Omega^* \mid \Omega^* \mathbin{U} \Omega^*$$

### Definition 8.3 (TLA+ Embedding)

| TLA+ Concept | VCA Encoding |
|--------------|--------------|
| State | ℱ^(n) |
| Variable | Slot v ∈ V^(n) |
| Action | δ ∈ Δ |
| Init | ℱ^(0) predicate |
| Next | ∃δ ∈ Δ : valid(δ, ℱ) |
| □φ | □φ (identical) |
| Spec | Ω* = Init ∧ □[Next] |

---

## Part II: Theorems with Complete Proofs

---

## 9. L0 Theorems (Structure)

### Theorem 1: Shallow Access

#### Statement

For all Kinds K in the base registry, the interpretation function I_K accesses only (V_ℛ, τ_ℛ), never (A_ℛ, ℛ.ℛ).

Formally, I_K depends only on:
- r ∈ V_ℛ (the rule slot)
- τ_ℛ(r) (the rule slot's type)
- t_s, t_t ∈ T (source and target types from the *current* system)
- i ∈ I (position index)

It never accesses:
- A_ℛ (relations within the rule system)
- ℛ.ℛ (the rule system's rule system)

#### Proof

By case analysis on base Kinds (Axiom Σ.6).

**Case K = Any:**
I_Any(r, t_s, t_t, i) = true. Returns constant. Accesses nothing.

**Case K = None:**
I_None(r, t_s, t_t, i) = false. Returns constant. Accesses nothing.

**Case K = PatternMatch:**
I_PatternMatch(r, t_s, t_t, i) = match(π_s, t_s) ∧ match(π_t, t_t) ∧ χ(i)
where (π_s, π_t, χ) = τ_ℛ(r).meta

Accesses: τ_ℛ(r).meta, t_s, t_t, i. Does not access A_ℛ or ℛ.ℛ.

**Case K = Eq:**
I_Eq(r, t_s, t_t, i) = (i = i_eq) ∧ (id(t_s), id(t_t)) ∈ E
where (i_eq, E) = τ_ℛ(r).meta

Accesses: τ_ℛ(r).meta, t_s, t_t, i. Does not access A_ℛ or ℛ.ℛ.

**Extension Kinds:** Must satisfy shallow access as registration requirement. ∎

#### Significance

Shallow access enables the infinite tower:
1. Checking admissibility at level n requires only level n-1's (V, τ)
2. No recursion into level n-2 or below
3. Each level can be checked independently

#### Dependencies
- Axiom Σ.5, Σ.6, Σ.7

#### Used By
- Theorem 2, Theorem 5

---

### Theorem 2: Self-Reference Coherence

#### Statement

For self-referential ℱ (where ℛ = ℱ):

$$\mathcal{F} \in \mathsf{FS}_{\text{coh}} \iff \mathcal{F} \in \mathsf{FS}_{\text{struct}} \land \text{all } A \text{ admissible}$$

The third coherence condition (ℛ ∈ FS_coh) becomes redundant.

#### Proof

**Direction (⟹):** Assume ℱ ∈ FS_coh. By Definition 4.2: ℱ ∈ FS_struct and all A admissible.

**Direction (⟸):** Assume ℱ ∈ FS_struct and all A admissible.

By Definition 4.2, we need condition 3. Since ℛ = ℱ, condition 3(b) applies directly.

**Why no recursive verification?**

If 3(b) required "ℛ = ℱ and ℱ ∈ FS_coh", we'd have:
ℱ ∈ FS_coh ⟺ struct ∧ admissible ∧ ℱ ∈ FS_coh (circular!)

**Resolution via Theorem 1:** Checking admissibility of A under ℛ = ℱ uses only (V, τ), never (A, ℛ). The admissibility check doesn't recurse—it examines structure, not relations.

**Coinductive interpretation:** Coherence for self-referential systems is the greatest fixed point:
Φ(X) = {ℱ | ℱ ∈ FS_struct ∧ all A admissible ∧ (ℛ = ℱ ⟹ ℱ ∈ X)}

The gfp is: {ℱ | ℱ ∈ FS_struct ∧ all A admissible} ∎

#### Significance

Self-reference doesn't create paradoxes because admissibility is about *types*, not *relations*.

#### Dependencies
- Theorem 1, Definition 4.1, 4.2

#### Used By
- Theorem 6, 7, 9

---

### Theorem 3: Structural Validity Decidable

#### Statement

For finite ℱ: "ℱ ∈ FS_struct" is decidable.

#### Proof

By Definition 4.1, ℱ ∈ FS_struct iff four conditions hold:

**Condition 1: V ≠ ∅** — O(1), decidable

**Condition 2: τ : V → T total** — O(|V|), check each element

**Condition 3: Position uniqueness** — O(|A|) with hash map

**Condition 4: Upper bounds** — O(|A| + |V|), count and compare

**Combined:** O(|V| + |A|), decidable ∎

#### Dependencies
- Definition 4.1, finiteness

#### Used By
- Theorem 4, 7, 9

---

### Theorem 4: Admissibility Decidable

#### Statement

For finite ℱ and ℛ: "(u,v,i) is admissible under ℛ" is decidable.

#### Proof

By Definition 3.1, (u,v,i) admissible iff ∃r ∈ V_ℛ with τ_ℛ(r).family = Rule and I_K(r, τ(u), τ(v), i) = true.

**Algorithm:**
```
for r in {r ∈ V_ℛ | τ_ℛ(r).family = Rule}:
    K = τ_ℛ(r).kind
    if I_K(r, τ(u), τ(v), i): return true
return false
```

**Termination:** V_ℛ finite, loop bounded.

**Decidability of I_K:** All base Kinds decidable (constant, pattern match, equality).

**Complexity:** O(|V_ℛ| · m) per relation, O(|A| · |V_ℛ| · m) for all. ∎

#### Dependencies
- Definition 3.1, Axiom Σ.5, Σ.6

#### Used By
- Theorem 7, 9

---

## 10. Tower Theorems

### Theorem 5: Tower Independence

#### Statement

Coherence at level n depends only on levels n and n-1 (for n > 0).

From ℱ^(n-1), we access only (V^(n-1), τ^(n-1)), never (A^(n-1), ℛ^(n-1)).

#### Proof

Fix n > 0.

**Condition 1 (ℱ^(n) ∈ FS_struct):** References only V^(n), A^(n), τ^(n). Levels accessed: n only.

**Condition 2 (Admissibility):** Since ℛ^(n) = ℱ^(n-1), for (u,v,i) ∈ A^(n) admissible:
∃r ∈ V^(n-1) : I_K(r, τ^(n)(u), τ^(n)(v), i) = true

By Theorem 1, I_K accesses r ∈ V^(n-1), τ^(n-1)(r), types from level n, position i.
Does NOT access A^(n-1) or ℛ^(n-1) = ℱ^(n-2).

**Condition 3:** ℱ^(n-1) ∈ FS_coh verified at level n-1, not n. ∎

#### Corollaries
- Modifying level k doesn't affect verification of levels < k
- Modifying level k may affect levels > k

#### Significance

Tower independence makes the infinite tower tractable: each level checked in isolation with one level of context.

#### Dependencies
- Theorem 1, Definition 5.1, 5.2

#### Used By
- Theorem 6, 7

---

### Theorem 6: Tower Coherence Coinductive

#### Statement

Tower_coh is the greatest fixed point of local coherence checks.

Define Φ(X) = {𝒯 | local_coh(𝒯, 0) ∧ ∀n > 0 : local_coh(𝒯, n) ∧ 𝒯 ∈ X}

where:
- local_coh(𝒯, 0) = ℱ^(0) ∈ FS_struct ∧ all A^(0) admissible under ℱ^(0)
- local_coh(𝒯, n) = ℱ^(n) ∈ FS_struct ∧ all A^(n) admissible under ℱ^(n-1)

Then Tower_coh = gfp(Φ).

#### Proof

**Lattice:** (𝒫(𝒯), ⊆) is complete.

**Monotonicity:** X ⊆ Y ⟹ Φ(X) ⊆ Φ(Y).

**Knaster-Tarski:** gfp(Φ) exists.

**Characterization:** 𝒯 ∈ gfp(Φ) iff ∀n ∈ ℕ : local_coh(𝒯, n).

*Proof:* (⟹) From gfp = Φ(gfp). (⟸) Define X = {𝒯' | ∀n: local_coh(𝒯', n)}, show X ⊆ Φ(X).

**Match Definition 5.2:** By Theorem 2, ℱ^(0) ∈ FS_coh iff local_coh(𝒯, 0). ∎

#### Coinductive Interpretation

A tower is coherent if we can never find a level that violates local coherence. This is safety: "nothing bad ever happens."

#### Dependencies
- Theorem 2, 5, Knaster-Tarski

#### Used By
- Theorem 7, 16

---

### Theorem 7: Finite Prefix Decidable

#### Statement

For any finite n, coherence of levels 0, ..., n is decidable.

#### Proof

**Algorithm:**
```
// Level 0
if not is_struct(F[0]): return false
if not all_admissible(F[0], F[0]): return false

// Levels 1 to n
for k from 1 to n:
    if not is_struct(F[k]): return false
    if not all_admissible(F[k], F[k-1]): return false
return true
```

**Termination:** n+1 iterations, each calls is_struct (Thm 3) and all_admissible (Thm 4).

**Complexity:** O(n · A · V · m) assuming bounded level sizes. ∎

#### Corollaries
- Finite systems: fully decidable
- Incremental: extending check costs O(a_{n+1} · v_n · m)

#### Significance

Bridge between infinite structure and finite verification.

#### Dependencies
- Theorem 2, 3, 4, 5

#### Used By
- Theorem 15, implementation

---

## 11. L1 Theorems (Δ)

### Theorem 8: Δ Preserves Structure

#### Statement

For ℱ ∈ FS_struct and valid δ: δ(ℱ) ∈ FS_struct.

#### Proof

By case analysis on each primitive δ ∈ Δ = {InsertSlot, DeleteSlot, Attach, Detach, Retype}.

**Case InsertSlot(v_new, t):**
- Preconditions: v_new ∉ V, t ∈ T
- Effect: V' = V ∪ {v_new}, τ' = τ ∪ {v_new ↦ t}
- (1) V' ≠ ∅: V' ⊇ V ≠ ∅
- (2) τ' total: extends τ
- (3) Position uniqueness: A unchanged
- (4) Upper bounds: Src(v_new) = ∅

**Case DeleteSlot(v_del):**
- Preconditions: v_del ∈ V, |V| > 1
- Effect: V' = V \ {v_del}, A' removes incident, τ' = τ|_V'
- (1) V' ≠ ∅: |V'| ≥ 1
- (2) τ' total: restriction of total
- (3) Position uniqueness: A' ⊆ A
- (4) Upper bounds: |Src'(v)| ≤ |Src(v)|

**Case Attach(u, v, i):**
- Preconditions: u,v ∈ V, position (v,i) free, |Src(v)| + 1 ≤ τ(v).upper
- Effect: A' = A ∪ {(u,v,i)}
- (1-2) V, τ unchanged
- (3) Position uniqueness: (v,i) was free
- (4) Upper bounds: precondition ensures

**Case Detach(u, v, i):**
- Preconditions: (u,v,i) ∈ A
- Effect: A' = A \ {(u,v,i)}
- (1-2) V, τ unchanged
- (3) Position uniqueness: A' ⊆ A
- (4) Upper bounds: |Src'| ≤ |Src|

**Case Retype(v, t_new):**
- Preconditions: v ∈ V, |Src(v)| ≤ t_new.upper
- Effect: τ' = τ[v ↦ t_new]
- (1) V unchanged
- (2) τ' total: update preserves totality
- (3) A unchanged
- (4) Upper bounds: precondition ensures ∎

#### Significance

Transitions preserve shape. Coherence may change, but structure is maintained.

#### Dependencies
- Definition 4.1, 7.1

#### Used By
- Theorem 9, 12

---

### Theorem 9: Core* Produces Coherent

#### Statement

For ℱ ∈ FS_struct: Core*(ℱ) ∈ FS_coh.

#### Definitions

**Core_R(ℱ):** Remove invalid rule slots and incident relations.
**Core(ℱ):** Remove inadmissible relations.
**Core*:** = Core ∘ Core_R (non-self-ref) or fixed point iteration (self-ref).

#### Proof

**Case ℛ = ∅ or ℛ ∈ FS_coh:**
1. Core_R removes invalid rule slots → ℱ₁
2. Core removes inadmissible relations → ℱ'
3. ℱ' ∈ FS_struct (subsets preserve)
4. All A' admissible by construction
5. ℛ condition satisfied

**Case ℛ = ℱ (self-referential):**

Define iteration: S₀ = (V, A), S_{n+1} = Φ(S_n) where Φ applies Core_R then Core.

**Decreasing:** V_{n+1} ⊆ V_n, A_{n+1} ⊆ A_n (only removes).

**Stabilizes:** Finite sets, decreasing sequences stabilize at some k.

**Fixed point:** S_k = S_{k+1} defines ℱ* = (V*, A*, τ|_V*, ℱ*).

**Verification:**
- ℱ* ∈ FS_struct: subset properties
- All A* admissible: fixed point of Core
- By Theorem 2: self-ref coherence ∎

#### Complexity
- Non-self-ref: O(|V| + |A| · |V_ℛ| · m)
- Self-ref: O((|V| + |A|)² · m)

#### Dependencies
- Theorem 2, 3, 4, Definition 4.2

#### Used By
- Theorem 10, 12

---

### Theorem 10: Core* Idempotent

#### Statement

Core*(Core*(ℱ)) = Core*(ℱ)

#### Proof

Let ℱ* = Core*(ℱ). By Theorem 9, ℱ* ∈ FS_coh.

Apply Core* to ℱ*:
- Core_R finds no invalid rule slots (already removed)
- Core finds no inadmissible relations (already removed)
- Both operations are no-ops on coherent systems

For self-referential: ℱ* is a fixed point of Φ, so Φ(ℱ*) = ℱ*. ∎

#### Significance

Core* is a projection onto FS_coh. "Already coherent" systems unchanged.

#### Dependencies
- Theorem 9

#### Used By
- Theorem 12

---

### Theorem 11: Independent Transitions Commute

#### Statement

If δ₁ ⊥ δ₂ (independent), then δ₁(δ₂(ℱ)) = δ₂(δ₁(ℱ)) whenever both defined.

#### Definitions

**R(δ):** Locations read by precondition.
**W(δ):** Locations written by effect.
**Independence:** δ₁ ⊥ δ₂ iff W(δ₁) ∩ R(δ₂) = ∅, W(δ₁) ∩ W(δ₂) = ∅, R(δ₁) ∩ W(δ₂) = ∅.

#### Proof

**Step 1: Preconditions preserved**
W(δ₁) ∩ R(δ₂) = ∅ ⟹ δ₁ doesn't modify what δ₂ reads.
δ₂ valid on ℱ ⟹ δ₂ valid on δ₁(ℱ). Symmetric.

**Step 2: Effects independent**
W(δ₁) ∩ W(δ₂) = ∅ ⟹ disjoint writes.

**Step 3: Final states equal**
- V: Disjoint slot operations commute
- A: Disjoint relation operations commute
- τ: Disjoint type updates commute
- ℛ: Unchanged or both paths give same self-ref

Therefore ℱ₁₂ = ℱ₂₁. ∎

#### Corollary (Diamond Property)

```
        F
       / \
     δ₁   δ₂
     /     \
   F₁       F₂
     \     /
      δ₂ δ₁
       \ /
       F*
```

#### Significance

Enables parallel execution, reordering, CRDT semantics.

#### Dependencies
- Definition 7.1, 7.3, 7.4

#### Used By
- Theorem 12

---

### Theorem 12: Replay Convergence

#### Statement

For replicas with same transaction set H and initial state ℱ₀:

replay(H, ℱ₀)_replica₁ = replay(H, ℱ₀)_replica₂

#### Definitions

**Transaction T:** (ops, origin, vc, seq)
**Order ≺:** Lexicographic on (vc, origin, seq) — total order.
**sort(H):** Transactions in ≺ order.
**eval(T, ℱ):** Apply ops with Core* after each.
**replay(H, ℱ₀):** eval(T_k, ...eval(T₁, ℱ₀)...) where sort(H) = [T₁,...,T_k].

#### Proof

**Step 1: sort(H) deterministic**
≺ is total, (vc, origin, seq) unique per transaction.

**Step 2: eval deterministic**
- Each δ is a partial function
- Core* is a function (Theorem 9)
- Composition deterministic

**Step 3: replay deterministic**
Deterministic sort + deterministic eval = deterministic replay.

**Step 4: Same computation**
Same H, same ℱ₀, same deterministic function ⟹ same result. ∎

#### Invalid Transition Policies
- Skip: Same δ skipped at both replicas
- Abort Transaction: Same T skipped
- Core* and Retry: Same Core* result

All deterministic.

#### CRDT Connection

State = (ℱ, H), Merge = union histories then replay.
- Commutative: H₁ ∪ H₂ = H₂ ∪ H₁
- Associative: (H₁ ∪ H₂) ∪ H₃ = H₁ ∪ (H₂ ∪ H₃)
- Idempotent: H ∪ H = H

#### Dependencies
- Theorem 8, 9, 10

---

## 12. L2 Theorems (Ω*)

### Theorem 13: □ is Coinductive

#### Statement

𝒯 ⊨ □φ iff ∀n ∈ ℕ : φ(ℱ^(n))

The always operator □ is coinductive: satisfied iff we never find a violation.

#### Proof

**Universal quantification:** □φ ≡ ∀n : φ(ℱ^(n)) = φ(ℱ^(0)) ∧ φ(ℱ^(1)) ∧ ...

**Coinductive characterization:**
Define Ψ(X) = {𝒯 | φ(ℱ^(0)) ∧ tail(𝒯) ∈ X}

Claim: {𝒯 | 𝒯 ⊨ □φ} = gfp(Ψ).

*Proof:*
- (⊆) If 𝒯 ⊨ □φ, then φ(ℱ^(0)) and tail(𝒯) ⊨ □φ.
- (⊇) If 𝒯 ∈ gfp(Ψ), apply tail repeatedly: ∀n : φ(ℱ^(n)). ∎

#### Operational Interpretation

Check φ(ℱ^(0)), φ(ℱ^(1)), ... If ever false, 𝒯 ⊭ □φ. If never false, 𝒯 ⊨ □φ (coinductively).

#### Connection to Theorem 6

Tower coherence: 𝒯 ∈ Tower_coh ⟺ 𝒯 ⊨ □(local_coh).

#### Dependencies
- Definition 8.1, Theorem 6, Knaster-Tarski

#### Used By
- Theorem 15, 16

---

### Theorem 14: ◇ is Inductive

#### Statement

𝒯 ⊨ ◇φ iff ∃n ∈ ℕ : φ(ℱ^(n))

The eventually operator ◇ is inductive (semi-decidable): satisfied iff we find a witness.

#### Proof

**Existential quantification:** ◇φ ≡ ∃n : φ(ℱ^(n)) = φ(ℱ^(0)) ∨ φ(ℱ^(1)) ∨ ...

**Inductive characterization:**
Define Ψ(X) = {𝒯 | φ(ℱ^(0)) ∨ tail(𝒯) ∈ X}

lfp(Ψ) = ∪_n Ψ^n(∅) = {𝒯 | ∃k : φ(ℱ^(k))}. ∎

**Duality:** 𝒯 ⊨ ◇φ ⟺ 𝒯 ⊭ □¬φ

#### Semi-Decidability

- **Positive:** If witness exists, found in finite time.
- **Negative:** Search may diverge forever.

◇φ is r.e., not decidable.

#### Bounded Variant

◇_{≤k}φ decidable: check levels 0..k.

#### Dependencies
- Definition 8.1, Theorem 13 (duality), Kleene

#### Used By
- Liveness specifications

---

### Theorem 15: SLA Finite Prefix Decidable

#### Statement

For Ω* without unbounded ◇: "𝒯 ⊨ Ω* up to level n" is decidable.

#### Definitions

**□-only fragment:** φ | □Ω* | Ω* ∧ Ω* | Ω* ∨ Ω* | ¬Ω* | ◇_{≤k}Ω*

**Satisfaction up to n:** Quantifiers range over {0,...,n}.

#### Proof

By structural induction on Ω*.

**Base φ:** Decidable state property on finite ℱ^(k).

**□Ψ:** 𝒯 ⊨_n □Ψ iff ∀k ≤ n : 𝒯,k ⊨ Ψ. Finite conjunction, IH applies.

**◇_{≤j}Ψ:** ∃k ≤ min(j,n) : 𝒯,k ⊨ Ψ. Finite disjunction.

**∧, ∨, ¬:** Standard closure under Boolean operations.

**Complexity:** O(|Ω*| · n^d · c) where d = nesting depth, c = base property cost. ∎

#### Practical SLA Patterns

| Pattern | Formula | Decidable |
|---------|---------|-----------|
| Always coherent | □coherent |
| Never exceed limit | □(count ≤ k) |
| Eventually respond | ◇responded | Semi |
| Respond within k | ◇_{≤k}responded |

#### Dependencies
- Theorem 7, 13, 14

---

### Theorem 16: Tower Satisfies SLA

#### Statement

𝒯 ∈ Tower_coh ⟹ 𝒯 ⊨ □(coherent)

A coherent tower satisfies the SLA "always coherent."

#### Proof

By Definition 5.2: 𝒯 ∈ Tower_coh ⟺ ∀n : local_coh(𝒯, n)

By definition: coherent(ℱ^(n)) ⟺ local_coh(𝒯, n)

Therefore: 𝒯 ∈ Tower_coh ⟺ ∀n : coherent(ℱ^(n))

By Definition 8.1: 𝒯 ⊨ □(coherent) ⟺ ∀n : coherent(ℱ^(n))

Combining: 𝒯 ∈ Tower_coh ⟺ 𝒯 ⊨ □(coherent) ∎

#### Significance

Tower coherence *is* the SLA □(coherent). Structural and temporal views unified.

#### Dependencies
- Definition 5.2, 8.1, Theorem 6, 13, 15

---

## Part III: Summary

---

## 13. Axiom Summary

| # | Axiom | Domain | Statement |
|---|-------|--------|-----------|
| Σ.1 | Slots non-empty | V | V ≠ ∅ |
| Σ.2 | Relations position-unique | A | (u₁,v,i), (u₂,v,i) ∈ A ⟹ u₁ = u₂ |
| Σ.3 | Types parametric | τ | T = ∏_{d∈D} T_d^⊤⊥, τ : V → T total |
| Σ.4 | Rule system recursive | ℛ | ℛ ∈ {∅, ℱ, FS} |
| Σ.5 | Interpretation shallow | I_K | Accesses only (V_ℛ, τ_ℛ) |
| Σ.6 | Base Kinds defined | K | Any, None, PatternMatch, Eq |
| Σ.7 | Kind registry closed | K | Extension requires registration |

---

## 14. Theorem Summary

### L0 Theorems (Structure)

| # | Theorem | Statement | Key Insight |
|---|---------|-----------|-------------|
| 1 | Shallow Access | I_K accesses only (V_ℛ, τ_ℛ) | Enables infinite tower |
| 2 | Self-Reference Coherence | Self-ref needs only struct + admissible | No circularity paradox |
| 3 | Structural Validity Decidable | Checking FS_struct is O(|V|+|A|) | Base verification |
| 4 | Admissibility Decidable | Checking admissibility is O(|A|·|V_R|·m) | Core constraint verifiable |

### Tower Theorems

| # | Theorem | Statement | Key Insight |
|---|---------|-----------|-------------|
| 5 | Tower Independence | Level n depends only on n, n-1 | Localized checking |
| 6 | Tower Coherence Coinductive | Tower_coh = gfp(Φ) | Safety property |
| 7 | Finite Prefix Decidable | Any prefix verifiable in O(n·A·V·m) | Infinite → finite |

### L1 Theorems (Δ)

| # | Theorem | Statement | Key Insight |
|---|---------|-----------|-------------|
| 8 | Δ Preserves Structure | Valid δ: FS_struct → FS_struct | Shape preserved |
| 9 | Core* Produces Coherent | Core*(ℱ) ∈ FS_coh | Repair always works |
| 10 | Core* Idempotent | Core*(Core*(ℱ)) = Core*(ℱ) | Projection property |
| 11 | Independent Transitions Commute | δ₁ ⊥ δ₂ ⟹ order irrelevant | Enables parallelism |
| 12 | Replay Convergence | Same H, same ℱ₀ → same result | CRDT semantics |

### L2 Theorems (Ω*)

| # | Theorem | Statement | Key Insight |
|---|---------|-----------|-------------|
| 13 | □ Coinductive | □φ = gfp, never find violation | Safety = coinductive |
| 14 | ◇ Inductive | ◇φ = lfp, find witness | Liveness = inductive |
| 15 | SLA Finite Prefix Decidable | □-only SLAs decidable up to n | Bounded verification |
| 16 | Tower Satisfies SLA | Tower_coh ⟺ □(coherent) | Coherence is SLA |

---

## 15. Dependency Graph

```
Axioms Σ.1-Σ.7
      │
      ▼
Theorem 1 (Shallow Access)
      │
      ├──────────────────┐
      ▼                  ▼
Theorem 2              Theorem 5
(Self-Ref)             (Tower Independence)
      │                  │
      │    ┌─────────────┤
      ▼    ▼             ▼
Theorem 3  Theorem 4   Theorem 6
(Struct)   (Admiss)    (Coinductive)
      │         │        │
      └────┬────┘        │
           ▼             │
      Theorem 7 ◄────────┘
      (Finite Prefix)
           │
           ├─────────────┐
           ▼             ▼
      Theorem 8      Theorem 15
      (Δ Struct)     (SLA Decidable)
           │             │
           ▼             ▼
      Theorem 9      Theorem 16
      (Core*)        (Tower SLA)
           │
           ├──────┬──────┐
           ▼      ▼      ▼
      Thm 10  Thm 11  Thm 12
      (Idemp) (Comm)  (Replay)
```

---

## 16. Projection Summary

VCA projects onto simpler systems by forgetting structure:
```
        VCA (V, A, τ, ℛ)
              │
    ┌─────────┼─────────┬───────────┐
    ↓         ↓         ↓           ↓
  DAGs      Types      R/W      Temporal
    ↓                   ↓           ↓
 λ-calculus         Effects      TLA+
```

| System | Level | Projection (↠) | Verified By | Prior Art |
|--------|-------|----------------|-------------|-----------|
| λ-calculus | L0 | Forget τ, ℛ → DAG ≅ λ | Theorems 1-4 | Wadsworth 1971 |
| Type systems | L0 | τ dimensions | Theorems 3-4 | — |
| CRDTs | L1 | Independent Δ commute | Theorem 12 | Shapiro 2011 |
| Effect systems | L1 | R/W sets | Theorem 11 | — |
| TLA+ | L2 | States = ℱ, Actions = Δ | Theorems 13-16 | Lamport 1994 |

---

## 17. Complexity Summary

| Operation | Complexity | Theorem |
|-----------|------------|---------|
| Structural validity | O(|V| + |A|) | Thm 3 |
| Single admissibility | O(|V_ℛ| · m) | Thm 4 |
| All admissibility | O(|A| · |V_ℛ| · m) | Thm 4 |
| Finite prefix (n levels) | O(n · A · V · m) | Thm 7 |
| Core* (non-self-ref) | O(|V| + |A| · |V_ℛ| · m) | Thm 9 |
| Core* (self-ref) | O((|V| + |A|)² · m) | Thm 9 |
| SLA prefix check | O(|Ω*| · n^d · c) | Thm 15 |

Where m = max Kind interpretation cost, d = formula nesting depth, c = base property cost.

---

## 18. Mechanized Proofs

All 16 theorems verified in Coq 8.18+ with no `Admitted` proofs.

| File | Theorems |
|------|----------|
| Core.v | Definitions, FS_struct |
| Admissibility.v | 1-4 (Shallow, Self-Ref, Struct, Admiss) |
| Towers.v | 5-7 (Independence, Coinductive, Prefix) |
| Transitions.v | 8 (Δ Preserves) |
| CoreStar.v | 9-10 (Core* Coherent, Idempotent) |
| Commutativity.v | 11-12 (Commute, Replay) |
| Temporal.v | 13-16 (□, ◇, SLA, Tower SLA) |
| Lambda.v | 6.1-6.2 (λ Sound, Complete) |


---

## 19. References

1. Church, A. — λ-calculus (1936)
2. Wadsworth, C. — Semantics and pragmatics of the lambda-calculus (1971)
3. Lamport, L. — TLA+ (1994)
4. Shapiro, M. et al. — CRDTs (2011)
5. Tarski, A. — Lattice-theoretical fixpoint theorem (1955)
6. Kozen, D. — Results on the propositional μ-calculus (1983)

---

## 20. Future Work

1. **L3+** — User-defined extension levels
2. **Applications** — Distributed systems, smart contracts, verified compilers
3. **Performance** — Incremental verification algorithms
4. **Tooling** — IDE support for SLA specification and checking

---

## Appendix: Proof Artifact

| Item | Value |
|------|-------|
| Proof assistant | Coq 8.18.0 |
| Dependencies | None (stdlib only) |
| Admitted | 0 |
| LOC | ~2500 |
| Build | `make` |
| Files | Core.v, Admissibility.v, Transitions.v, Towers.v, CoreStar.v, Commutativity.v, Temporal.v, Lambda.v, Model.v |
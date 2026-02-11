# Stratified Coherence
# A classification theorem for self-referential constraint operators over general value spaces

**Version:** 2.0 (continuous extension)

**Abstract.** Stratified Coherence (SC) proves when self-referential constraint systems over a value space V can achieve coherent total valuation. The theory identifies structural conditions — admissibility, diagonal-compatibility, absence of couplings, and target-consistency — that are individually necessary and jointly sufficient for robust determination: unique total valuation resilient under compatible extensions. The central result is that non-admissible diagonal constraints (those referencing the value being defined) are structurally incoherent when Fix(σ) = ∅, forced-equilibrium when Fix(σ) is a singleton, and indeterminate otherwise. Robust determination requires exactly four conditions; no subset suffices. This version extends the original Boolean (V = {⊤,⊥}) theory to arbitrary complete metric value spaces, recovering the discrete case as a special instance.

**Changes from v1.0:** Value space generalized from {⊤,⊥} to (V, d). Involutions σ replace Boolean negation ¬. Constraint types unified: target(t), diag(σ), coupled(σ). Per-constraint feasibility (Feas), solution set (Sol), and coherence partition (CP) replace conflict-freedom. Lethality theory added (§9). Classification theorem (§13) reduced from six conditions to four: S* and stratification-for-non-diagonals proved unnecessary.

---

## 1. Overview

### 1.1 Problem

Coordination systems that reference their own state face a fundamental structural problem: self-referential constraints can create configurations where no consistent total assignment exists. SC identifies the exact boundary between coherent and incoherent self-referential constraint systems.

### 1.2 Main Result

**Theorem (Robust Determination, §13.2).** A constraint system ℱ is robustly determined — admits a unique total valuation resilient under all compatible extensions — if and only if:

1. All diagonals are admissible (ℓ(c) < ℓ(target(c)))
2. Diagonal-compatible (all admissible diagonals targeting the same coordinate agree; all agree with any target constraint)
3. No same-level couplings
4. Target-consistent (no coordinate receives conflicting target demands)

### 1.3 Proof Method

Sufficiency: transfinite induction on levels, processing constraints by target level. Each coordinate's feasible set is shown to be a singleton.

Necessity: contrapositive — violating any condition either produces immediate incoherence (Feas = ∅), indeterminacy (|Sol| > 1), or fragility under admissible extension.

### 1.4 Scope

SC operates within a specific semantic regime: total valuations over a complete metric space V, persistent constraints, self-referential diagonal operators via continuous involutions, and stratification over a well-founded level poset. All theorems are proved within this regime. Appendix A situates SC relative to adjacent semantic frameworks.

### 1.5 Classical Recovery

When V = {⊤, ⊥} with discrete metric and σ = ¬ (Boolean negation), all definitions, theorems, and proofs specialize to the original Boolean SC. Each section includes explicit recovery statements.

---

## 2. Primitives

### 2.1 Constraint System

A constraint system is a tuple ℱ = (S, I, C, ℓ) where:

- **S** is a set of slots
- **I** is an index set
- **ℓ : S → L** assigns each slot a level in a well-founded poset (L, ≤) with minimum ⊥
- **C** is a finite set of constraints

### 2.2 Coordinates

A **coordinate** is a triple q = (u, v, i) ∈ S × S × I.

The **level of a coordinate** is:

$$\ell(q) := \ell(u, v, i) := \max(\ell(u), \ell(v))$$

### 2.3 Value Space

A **value space** is a tuple (V, d, e) where:

- V is a set with |V| ≥ 2
- d : V × V → ℝ≥0 is a metric
- (V, d) is complete (every Cauchy sequence converges)
- e ∈ V is a distinguished **default value**

**Standard instances:**

| Instance | V | d | e | Notes |
|----------|---|---|---|-------|
| Boolean | {⊤, ⊥} | discrete | ⊥ | Classical SC |
| Unit interval | [0, 1] | \|x − y\| | 0 | Continuous SC |
| Bounded lattice | Any | lattice metric | min | General |

### 2.4 Involutions

An **involution** on V is a continuous function σ : V → V such that σ(σ(x)) = x for all x ∈ V.

The **fixed-point set** of σ is:

$$\text{Fix}(\sigma) := \{x \in V : \sigma(x) = x\}$$

**Standard instances:**

| Instance | V | σ | Fix(σ) | Notes |
|----------|---|---|--------|-------|
| Boolean negation | {⊤, ⊥} | ¬ | ∅ | Fixed-point-free |
| Complement | [0, 1] | 1 − x | {0.5} | Unique fixed point |
| Reflection about p | [0, 1] | 2p − x (clamped) | {p} | Unique fixed point |
| Identity | V | id | V | Every point fixed |

**Topological constraint.** On connected V ⊆ ℝⁿ, every continuous involution has Fix(σ) ≠ ∅ (intermediate value theorem for n = 1; Brouwer for general n). Fixed-point-free involutions exist only on disconnected V (e.g., {⊤, ⊥}).

### 2.5 Constraints

A constraint is a tuple c = (target(c), τ(c), ℓ(c)) where:

- target(c) ∈ S × S × I — the coordinate constrained
- τ(c) ∈ {target(t), diag(σ), coupled(σ, q_s)} — constraint type
- ℓ(c) ∈ L, ℓ(c) > ⊥ — constraint level

**Constraint types:**

| Type | Parameters | Meaning |
|------|-----------|---------|
| target(t) | t ∈ V | Demands α(q) = t |
| diag(σ) | σ involution on V | Demands α(q) = σ(α_{≤ℓ(c)}(q)) |
| coupled(σ, q_s) | σ involution, q_s source | Demands α(q_t) = σ(α(q_s)) at same level |

**Classical notation recovery:**

| Classical | General |
|-----------|---------|
| (+) | target(⊤) |
| (−) | target(⊥) |
| diag | diag(¬) where ¬ is Boolean negation |

### 2.6 Matching

Constraint c **matches** coordinate q, written c ▷ q, iff target(c) = q.

$$M(q) := \{c \in C : c \triangleright q\}$$

### 2.7 Valuations

A **valuation** is a total function:

$$\alpha : S \times S \times I \to V$$

The **default valuation** assigns e everywhere: α(q) = e for all q.

---

## 3. Stratification

### 3.1 Definition

ℱ is **stratified** iff:

$$\forall c \in C : \ell(c) \leq \ell(\text{target}(c))$$

### 3.2 Diagonal Admissibility

A diagonal constraint c (with τ(c) = diag(σ)) is **admissible** iff:

$$\ell(c) < \ell(\text{target}(c))$$

A diagonal constraint c is **non-admissible** iff:

$$\ell(c) \geq \ell(\text{target}(c))$$

Non-admissible diagonals are either **same-level** (ℓ(c) = ℓ(target(c))) or **downward** (ℓ(c) > ℓ(target(c))).

### 3.3 Role of Stratification

Stratification serves two independent roles:

| Role | Description | Where used |
|------|-------------|------------|
| Prefix consistency | Ensures α_{≤k} captures all constraints targeting levels ≤ k | §4 (constructive semantics) |
| Diagonal admissibility | ℓ(c) < ℓ(target(c)) for diagonals | §3.2, §11 (necessity) |

For determination and robustness (§12–§13), only diagonal admissibility is load-bearing. The condition "admissible-only" (all diagonals admissible) is strictly stronger than "stratified for diagonals." Stratification of non-diagonal constraints is not referenced in any determination or robustness proof. See §13.4 for the full analysis.

---

## 4. Constructive Semantics

### 4.1 Level-Restricted Systems

For k ∈ L:

$$C_{\leq k} := \{c \in C : \ell(c) \leq k\}$$
$$\mathcal{F}_{\leq k} := (S, I, C_{\leq k}, \ell)$$

**Note.** Under full stratification (§3.1), C_{≤k} captures all constraints whose targets have level ≤ k. Without stratification for non-diagonals, C_{≤k} may miss downward non-diagonal constraints. This affects prefix consistency (§4.3) but not determination (§12).

### 4.2 The SC Construction

Define α : S × S × I → V by transfinite recursion on L.

**Base.** For coordinates q with ℓ(q) = ⊥: Set α(q) = e. No constraints target level ⊥.

**Recursion.** At level j > ⊥, assuming α is defined at all levels < j:

For each coordinate q with ℓ(q) = j:

**Step 1.** Compute Demands(q).

For each c ∈ M(q):

$$\text{demand}(c, \alpha) := \begin{cases}
t & \text{if } \tau(c) = \text{target}(t) \\
\sigma(\alpha_{\leq \ell(c)}(q)) & \text{if } \tau(c) = \text{diag}(\sigma)
\end{cases}$$

$$\text{Demands}(q) := \{\text{demand}(c, \alpha) : c \in M(q)\}$$

**Step 2.** Set α(q).

$$\alpha(q) := \begin{cases}
e & \text{if } M(q) = \emptyset \\
x & \text{if } \text{Demands}(q) = \{x\} \\
x^* & \text{if same-level diagonal with unique fixed point } x^* \text{ (§4.5)} \\
\textbf{undefined} & \text{if } \text{diam}(\text{Demands}(q)) > 0 \text{ and no resolution}
\end{cases}$$

### 4.3 Definition of α_{≤k}

The **level-k valuation** α_{≤k} : S × S × I → V is defined as:

$$\alpha_{\leq k}(q) := \begin{cases}
\alpha^{(k)}(q) & \text{if } \ell(q) \leq k \\
e & \text{if } \ell(q) > k
\end{cases}$$

where α^{(k)} is the SC construction applied to ℱ_{≤k}, restricted to coordinates at level ≤ k.

**Prefix consistency.** Under full stratification: α_{≤j} agrees with α_{≤k}|_{≤j} for j ≤ k. This property requires stratification of non-diagonal constraints (§3.3).

### 4.4 Diagonal Classification

**Theorem 4.1 (Non-Admissible Diagonal Classification).** Let c be a non-admissible diagonal with involution σ, at level k, targeting q with ℓ(q) = j ≤ k. Then:

1. If Fix(σ) = ∅: ℱ is **incoherent** at q.
2. If Fix(σ) = {x\*}: q is forced to x\*. Coherence depends on compatibility of x\* with other demands at q.
3. If |Fix(σ)| > 1: q requires a selection principle. Without one, ℱ is **indeterminate** at q.

*Proof.*

Let c be diagonal with τ(c) = diag(σ) at level k targeting q with ℓ(q) = j ≤ k.

**Case 1: Same-level (k = j).**

demand(c) = σ(α_{≤k}(q)) = σ(α^{(k)}(q)).

Since ℓ(q) = k, the SC construction computes α^{(k)}(q) at level k. Constraint c ∈ M_{≤k}(q), so Demands includes σ(α^{(k)}(q)).

**Subcase 1a: M_{≤k}(q) = {c}.** α^{(k)}(q) = σ(α^{(k)}(q)). Fixed-point equation. Solutions: Fix(σ). Classification by |Fix(σ)|. ∎

**Subcase 1b: |M_{≤k}(q)| > 1.** Let c' ∈ M_{≤k}(q), c' ≠ c, with demand(c') = v. For consistency: σ(α(q)) = v, so α(q) = σ(v). Also α(q) ∈ Fix(σ), so σ(v) ∈ Fix(σ), so v ∈ Fix(σ). If v ∉ Fix(σ): incoherent. If v ∈ Fix(σ): forced to v. ∎

**Case 2: Downward (k > j).** Same fixed-point equation arises. Classification follows Case 1. ∎

**Corollary 4.2 (Classical Recovery).** When V = {⊤, ⊥} and σ = ¬, Fix(σ) = ∅. Every non-admissible diagonal is incoherent. Recovers original Theorem 4.1.

### 4.5 Same-Level Resolution

When a same-level diagonal with involution σ targets q and Fix(σ) ≠ ∅:

- **Unique resolution.** Fix(σ) = {x\*} and all other demands at q equal x\*: α(q) = x\*.
- **Compatible resolution.** |Fix(σ)| > 1 and all other demands agree on some x\* ∈ Fix(σ): α(q) = x\*.
- **No resolution.** Other demands require v ∉ Fix(σ): incoherent (Theorem 4.1, Subcase 1b).

### 4.6 Admissible Diagonal Semantics

**Lemma 4.3.** If c is an admissible diagonal with involution σ at level k targeting q with ℓ(q) > k, then:

$$\text{demand}(c) = \sigma(e)$$

*Proof.* α_{≤k}(q) = e since ℓ(q) > k. Thus demand(c) = σ(e). ∎

**Corollary 4.4 (Classical Recovery).** When σ = ¬ on {⊤, ⊥}: demand(c) = ¬⊥ = ⊤. Recovers original Lemma 4.3.

---

## 5. Conflict-Free (Inductive Definition)

### 5.1 Definition by Transfinite Induction

ℱ is **conflict-free at level j** iff:

1. ℱ is conflict-free at all levels < j, and
2. For all q with ℓ(q) = j: diam(Demands(q)) = 0, where Demands(q) is computed using α_{<j}.

Here diam(∅) = 0 and diam({x}) = 0.

diam(Demands(q)) := sup{d(a, b) : a, b ∈ Demands(q)}.

**Base:** ℱ is conflict-free at level ⊥ iff true (vacuously — no constraints target ⊥).

**Definition:** ℱ is **conflict-free** iff ℱ is conflict-free at all levels in L.

**Classical recovery.** When V = {⊤, ⊥} with d(⊤, ⊥) = 1: diam(Demands(q)) = 0 iff |Demands(q)| ≤ 1. Recovers original §5.1.

### 5.2 Well-Foundedness

**Theorem 5.1.** The definition of conflict-free is well-founded.

*Proof.* L is well-founded with minimum ⊥. At each level j, conflict-freedom depends only on levels < j. By transfinite induction, well-defined for all j. ∎

---

## 6. Coherence

### 6.1 Satisfaction

A valuation α : S × S × I → V **satisfies** constraint c iff:

$$\text{sat}(c, \alpha) := \begin{cases}
\alpha(q) = t & \text{if } \tau(c) = \text{target}(t) \text{ at } q \\
\alpha(q) = \sigma(\alpha_{\leq k}(q)) & \text{if } \tau(c) = \text{diag}(\sigma) \text{ at } q, \ell(c) = k \\
\alpha(q_t) = \sigma(\alpha(q_s)) & \text{if } \tau(c) = \text{coupled}(\sigma) \text{ from } q_s \text{ to } q_t
\end{cases}$$

### 6.2 Solution Set

$$\text{Sol}(\mathcal{F}) := \{\alpha : S \times S \times I \to V \mid \forall c \in C : \text{sat}(c, \alpha)\}$$

### 6.3 Coherence Classification

| Sol(ℱ) | Classification |
|---------|---------------|
| ∅ | **Incoherent** |
| {α} | **Determined** |
| Finite, \|Sol\| > 1 | **Degenerate** |
| Manifold, dim > 0 | **Mode-coherent** (dim = number of free modes) |

ℱ is **coherent** iff Sol(ℱ) ≠ ∅.

**Classical recovery.** When V = {⊤, ⊥}: Sol is finite. Mode-coherent cannot arise. With conflict-freedom, coherent ⟺ determined ⟺ unique total α.

### 6.4 Level Slice

For level j, given α_{<j}:

$$\text{CP}_j(\alpha_{<j}) := \{(x_q)_{q \in Q_j} \in V^{|Q_j|} : \forall c \text{ active at level } j, \text{sat}(c, \alpha_{<j} \cup x) \}$$

where Q_j = {q : ℓ(q) = j}.

| CP_j | Level status |
|------|-------------|
| ∅ | Lethal at level j |
| Single point | Determined at level j |
| dim(CP_j) > 0 | Modes present at level j |

### 6.5 Coherence Partition

$$\text{CP}(\mathcal{F}) := (\text{CP}_\bot, \text{CP}_1(\alpha_\bot), \text{CP}_2(\alpha_{\leq 1}), \ldots)$$

Each entry depends on valuations at prior levels. If CP_j = ∅ for some j, the partition is undefined above j.

### 6.6 Constructive Decomposition

**Theorem 6.1 (Constructive Decomposition).** [Structural]

If ℱ is stratified:

$$\text{Sol}(\mathcal{F}) \cong \text{CP}_\bot \times \text{CP}_1(\alpha_\bot) \times \text{CP}_2(\alpha_{\leq 1}) \times \cdots$$

Sol factors as a conditioned product of per-level slices.

*Proof.*

By stratification, every constraint c has ℓ(c) ≤ ℓ(target(c)). The satisfaction of c depends only on α_{≤ℓ(target(c))}. For each admissible case, constraint c contributes to CP_j for j = ℓ(target(c)) and depends only on α_{<j} and assignments within level j. Therefore Sol decomposes: an element of Sol is a choice from CP_⊥, then CP_1 conditioned on that, then CP_2, etc.

If all CP_j are singletons: Sol = {unique α}. Determined.
If some CP_j has dim > 0: Sol has at least that dimension. Mode-coherent.
If any CP_j = ∅: Sol = ∅. Incoherent. ∎

**Corollary 6.2 (Classical Recovery).** When V = {⊤, ⊥}, no couplings, all diagonals admissible: each CP_j ⊆ {⊤, ⊥}^{|Q_j|}. CP_j is singleton iff diam(Demands(q)) = 0 for all q ∈ Q_j. Recovers original pointwise coherence. ∎

---

## 7. Per-Constraint Feasibility

### 7.1 Feasible Set

For constraint c at coordinate q, given α_{<ℓ(q)}:

$$\text{Feas}(c) := \{v \in V : v \text{ satisfies } c \text{ given } \alpha_{<\ell(q)}\}$$

| Constraint type | Feas(c) |
|----------------|---------|
| target(t) | {t} |
| diag(σ), admissible (ℓ(c) < ℓ(q)) | {σ(e)} |
| diag(σ), same-level (ℓ(c) = ℓ(q)) | Fix(σ) |
| diag(σ), downward (ℓ(c) > ℓ(q)) | Fix(σ) |
| coupled(σ, q_s), ℓ(q_s) < ℓ(q_t) | {σ(α(q_s))} (known from below) |

### 7.2 Constraint Status

| Feas(c) | Status | Interpretation |
|---------|--------|----------------|
| ∅ | **Lethal** | No value satisfies c |
| {v} singleton | **Attracted** to v | Unique forced value |
| |Feas| > 1 | **Open** | Multiple values permitted |

### 7.3 Per-Coordinate Feasible Set

$$F(q) := \bigcap_{c \in M(q)} \text{Feas}(c)$$

If F(q) = ∅, coordinate q is lethal. If F(q) = {v}, coordinate q is determined. If |F(q)| > 1, coordinate q has free modes.

---

## 8. Diagonal Compatibility

### 8.1 Motivation

By Lemma 4.3, an admissible diagonal with involution σ demands σ(e). If two admissible diagonals at the same coordinate have σ₁(e) ≠ σ₂(e), or if an admissible diagonal's demand disagrees with a target, the coordinate is lethal.

### 8.2 Definition

ℱ is **diagonal-compatible** iff for every coordinate q:

1. All admissible diagonals targeting q agree: if c₁, c₂ are admissible diagonals at q with involutions σ₁, σ₂, then σ₁(e) = σ₂(e).

2. All admissible diagonals agree with targets: if c is an admissible diagonal at q with involution σ and c' is target(t) at q, then σ(e) = t.

### 8.3 Consequence

**Lemma 8.1.** If ℱ is diagonal-compatible and contains only admissible diagonals, then no admissible diagonal conflicts with any target constraint.

*Proof.* Condition 2 of §8.2. ∎

**Classical recovery.** When σ = ¬ on {⊤, ⊥}: σ(e) = σ(⊥) = ⊤. Condition 2 requires: no target(⊥) at q if an admissible diagonal targets q. This is: no (−) constraints above level ⊥. Recovers original §7.2.

---

## 9. Lethality Theory

### 9.1 Intrinsic vs Emergent Lethality

**Intrinsic lethality:** Feas(c) = ∅ for a single constraint c. Requires Fix(σ) = ∅ for a non-admissible diagonal.

**Emergent lethality:** Each Feas(c) ≠ ∅, but ⋂ Feas(c) = ∅ for a set of constraints at the same coordinate.

**Corollary 9.1 (No Intrinsic Lethality on Connected V).** [Derived]

On connected V ⊆ ℝⁿ, Feas(c) ≠ ∅ for every individual constraint c. All lethality is emergent.

*Proof.* Targets: {t} ≠ ∅. Admissible diagonals: {σ(e)} ≠ ∅. Non-admissible diagonals: Fix(σ) ≠ ∅ by IVT (n = 1) or Brouwer (general n). ∎

### 9.2 Conflict Order

**Definition.** The **conflict order** of a lethal coordinate q is:

$$\kappa(q) := \min\{|K| : K \subseteq M(q), \bigcap_{c \in K} \text{Feas}(c) = \emptyset\}$$

| κ(q) | Meaning |
|------|---------|
| 1 | Intrinsic: single constraint with Feas = ∅ |
| 2 | Pairwise: two constraints incompatible |
| ≥ 3 | Higher-order: pairwise compatible, jointly lethal |

### 9.3 Lethality Source Classification

| V | κ = 1 possible? | κ = 2 | κ ≥ 3 |
|---|---|---|---|
| Discrete ({⊤,⊥}) | Yes (Fix(¬) = ∅) | Yes | No (all Feas are singletons) |
| Connected ⊆ ℝ | No (IVT) | Yes | Yes, if non-convex Fix sets |
| Compact convex ⊆ ℝⁿ | No (Brouwer) | Yes | Yes, if non-convex Fix sets |

### 9.4 Helly Bound

**Corollary 9.2 (Helly Bound).** [Derived]

If all Feas(c) at q are convex subsets of V ⊆ ℝⁿ, then κ(q) ≤ n + 1.

In particular, on V ⊆ ℝ¹ with convex Feas sets: κ ≤ 2. Every conflict is pairwise.

*Proof.* Helly's theorem. ∎

**Consequence for admissible-only systems.** Under admissible-only + target constraints, all Feas sets are singletons (convex). On V ⊆ ℝ¹, κ ≤ 2. Every conflict is pairwise and detectable by checking pairs. O(|M(q)|²) per coordinate.

---

## 10. Zone Conditions

### (L) Layer Openness

For any k > ⊥, there exist slots at level k.

### (D') Controlled Diagonal Availability

For each level k > ⊥, there exists at least one coordinate q with ℓ(q) > k such that a diagonal constraint at level k targeting q can be added without violating diagonal-compatibility of the extended system.

### (T) Totality

Valuations are total: α : S × S × I → V.

### (E) Persistence

Existing constraints remain when new constraints are added.

### (S*) Global Separation [Non-Triviality Condition]

For any level j, there exists a coordinate q at level > j not targeted by C_{≤j}.

**Role clarification.** S* is not required for coherence, determination, or robust determination (§12–§13). It is a richness condition ensuring that the zone admits non-trivial extensions under (D'). Without S*, the adversary in the robustness game may be blocked by saturation, making robustness vacuously satisfied. See §13.5 for the full analysis.

---

## 11. Necessity Theorem

### 11.1 Non-Admissible Diagonal Necessity

**Theorem 11.1.** If ℱ contains a non-admissible diagonal with Fix(σ) = ∅, then ℱ is incoherent.

*Proof.* Theorem 4.1, case 1. ∎

### 11.2 Corollary (Admissibility for Diagonals)

If ℱ is coherent and determined, then every diagonal in ℱ is either admissible or has |Fix(σ)| = 1 with x* compatible with all other demands.

*Proof.* If Fix(σ) = ∅: incoherent (Theorem 11.1). If |Fix(σ)| > 1: indeterminate (Theorem 4.1, case 3). If Fix(σ) = {x\*} but x\* incompatible with other demands: incoherent (Theorem 4.1, Subcase 1b). ∎

---

## 12. Sufficiency Theorems

### 12.1 Determined Sufficiency

**Theorem 12.1 (Determined Sufficiency).** [Structural]

If ℱ satisfies:
1. All diagonals admissible
2. Diagonal-compatible (§8.2)
3. No same-level couplings
4. Target-consistent (no coordinate has target(t₁) and target(t₂) with t₁ ≠ t₂)

Then Sol(ℱ) = {α} for a unique total α.

*Proof.* By transfinite induction on levels.

**Base (j = ⊥).** No constraints target level ⊥. M(q) = ∅ for all q with ℓ(q) = ⊥. α(q) = e. ∎

**Induction (j > ⊥).** Assume α_{<j} unique. For q with ℓ(q) = j:

Partition M(q) into:
- T(q) := {c ∈ M(q) : τ(c) = target(t)} — target constraints
- A(q) := {c ∈ M(q) : τ(c) = diag(σ), c admissible} — admissible diagonals
- N(q) := M(q) \ (T(q) ∪ A(q)) — non-admissible diagonals

By hypothesis 1, N(q) = ∅.

**Case M(q) = ∅:** F(q) = V. α(q) = e. Unique. ✓

**Case T(q) ≠ ∅, A(q) = ∅:** Target-consistency (hypothesis 4) ensures all targets demand the same t. F(q) = {t}. α(q) = t. Unique. ✓

**Case A(q) ≠ ∅, T(q) = ∅:** All admissible diagonals demand σ(e) (Lemma 4.3). Diagonal-compatibility condition 1 ensures all σ(e) agree. F(q) = {σ(e)}. Unique. ✓

**Case T(q) ≠ ∅, A(q) ≠ ∅:** Diagonal-compatibility condition 2 ensures t = σ(e). F(q) = {t}. Unique. ✓

All cases: F(q) singleton. α(q) unique. By transfinite induction, α total and unique. ∎

**Note.** Neither stratification-for-non-diagonals nor S* appears in any step.

### 12.2 General Sufficiency

**Theorem 12.2 (General Sufficiency).** [Schema]

If ℱ satisfies:
1. Stratified
2. Diagonal-compatible
3. All non-admissible diagonals have Fix(σ) ≠ ∅
4'. For every coordinate q: F(q) ≠ ∅
5. All same-level coupled components jointly feasible: CP_j^W ≠ ∅
6. Target-consistent

Then Sol(ℱ) ≠ ∅.

*Proof.* Transfinite induction. For uncoupled coordinates: F(q) ≠ ∅ by 4'. Pick x ∈ F(q). For coupled coordinates: CP_j^W ≠ ∅ by 5. Pick joint solution. Combined: α at level j defined. IH extends. ∎

**Why [Schema].** Hypotheses 4' and 5 are asserted, not derived from structural conditions. Verifying them requires V-specific arguments (Brouwer, Helly, etc.). Theorem 12.1 derives feasibility structurally; Theorem 12.2 assumes it.

**Gap.** Multiple non-admissible diagonals with pairwise-compatible Fix sets can have jointly empty intersection (§9.2, higher-order conflict). Hypothesis 4' absorbs this by asserting the full intersection is non-empty.

---

## 13. Classification Theorems

### 13.1 Pointwise Coherence

**Theorem 13.1 (Pointwise Coherence).** [Structural]

Under stratification:

$$\text{Sol}(\mathcal{F}) \neq \emptyset \iff \text{the sequential construction } x_\bot, x_1(x_\bot), x_2(x_{\leq 1}), \ldots \text{ never encounters } \text{CP}_j = \emptyset$$

*Proof.* Immediate from Theorem 6.1 (Constructive Decomposition).

(⇒) If Sol ≠ ∅, any α ∈ Sol decomposes into (x_j)_j with x_j ∈ CP_j(x_{<j}). No CP_j empty along that path.

(⇐) If the construction never encounters CP_j = ∅, it produces total α satisfying all constraints. ∎

**Uniform coherence.** ℱ is **uniformly coherent** iff ∀ compatible x_{<j}: CP_j(x_{<j}) ≠ ∅. Stronger than coherent. For determined systems, coherent = uniformly coherent (only one path).

### 13.2 Robust Determination

**Definition.** ℱ is **robustly determined** iff ℱ is determined and remains determined under all admissible extensions (D', E).

**Theorem 13.2 (Robust Determination).** [Structural]

$$\text{Robustly determined} \iff \text{Admissible-only} \land \text{Diagonal-compatible} \land \text{No couplings} \land \text{Target-consistent}$$

### 13.3 Proof of Theorem 13.2

**(⇐) Sufficiency.**

ℱ is determined by Theorem 12.1.

Let ℱ' = ℱ ∪ {c'} be an admissible extension. c' is either an admissible diagonal at level k targeting q with ℓ(q) > k, or a target(t) compatible with existing constraints.

**Case c' = admissible diag(σ') targeting q:**

Feas(c') = {σ'(e)}.

If M(q) = ∅: F'(q) = {σ'(e)}. Attracted. Determined. ✓

If M(q) ≠ ∅, q attracted to v: F'(q) = {v} ∩ {σ'(e)}. By diagonal-compatibility of the extended system ℱ' (required by the definition of admissible extension under (D')): σ'(e) = v. F'(q) = {v}. ✓

**Case c' = target(t) at q, compatible:** t agrees with existing demands. F'(q) unchanged or = {t}. ✓

No other coordinates affected. ℱ' determined. ∎

**(⇒) Necessity.** Contrapositive for each condition.

**Non-admissible diagonal with Fix(σ) = ∅:** Feas(c) = ∅. Incoherent. Not determined. ∎

**Non-admissible diagonal with Fix(σ) = {x\*}:** F(q) = {x\*}. Under (D'), add target(t ≠ x\*) at q. Diagonal-compatibility (§8.2) restricts targets relative to admissible diagonals only; non-admissible diagonals are not covered. So target(t ≠ x\*) is a valid extension. F'(q) = {x\*} ∩ {t} = ∅. Lethal. Not robustly determined. ∎

**Non-admissible diagonal with |Fix(σ)| > 1:** |F(q)| > 1. Underdetermined. Not determined. ∎

**Diagonal-compatibility condition 1 violated:** ∃ admissible diags with σ₁(e) ≠ σ₂(e). F(q) ⊆ {σ₁(e)} ∩ {σ₂(e)} = ∅. Already lethal. ∎

**Diagonal-compatibility condition 2 violated:** ∃ target(t) and admissible diag with t ≠ σ(e). F(q) = ∅. Already lethal. ∎

**Coupled constraints present:** If unique joint solution: add incompatible target at one coupled coordinate; coupling propagates conflict. If multiple solutions: underdetermined. ∎

**Target-consistency violated:** ∃ target(t₁), target(t₂) with t₁ ≠ t₂. F(q) = ∅. Already lethal. ∎

All four conditions necessary. ∎

### 13.4 Why Stratification Drops

Stratification (§3.1) requires ∀c: ℓ(c) ≤ ℓ(target(c)). For determination and robustness:

**For diagonals:** Admissibility requires ℓ(c) < ℓ(target(c)), which is strictly stronger. "Admissible-only" subsumes "stratified for diagonals."

**For non-diagonals:** The determination proof (Theorem 12.1) processes constraints by target level. Constraint level ℓ(c) of a non-diagonal constraint is never referenced — demand(c) = t is independent of ℓ(c). A downward target(t) at q with ℓ(c) > ℓ(q) contributes the same demand t as one with ℓ(c) ≤ ℓ(q).

For the necessity direction: the adversary cannot exploit a downward target(t) because diagonal-compatibility forces any admissible diagonal added at q to have σ(e) = t. The adversary's move is blocked.

Stratification survives only in §4 (prefix consistency: ensuring α_{≤k} is well-defined) and §6.6 (constructive decomposition). It is not a condition for determination or robust determination.

### 13.5 Why S* Drops

S* (§10) requires: ∀j, ∃ coordinate at level > j not targeted by C_{≤j}.

**Sufficiency direction:** Theorem 12.1 proves determination without referencing S*. No step requires untargeted coordinates to exist.

**Necessity direction:** Under admissible-only + diagonal-compatible + no couplings + target-consistent, every admissible extension is either:
- (a) Targets a free coordinate (M(q) = ∅): attracts it to σ(e). Harmless.
- (b) Targets an occupied coordinate: diagonal-compatibility forces σ(e) = v. No conflict.

In neither case does the extension break determination. This holds regardless of whether orthogonal (untargeted) slots exist. The adversary is constrained by diagonal-compatibility, not by the availability of targets.

Without S*, the adversary may be fully blocked (all coordinates occupied with values that force agreement). The system is robustly determined — for the right reason (structural compatibility), not the wrong reason (no room for extensions).

S* is a **richness condition** on the zone, not a coherence or determination condition. It may be relevant for other purposes (e.g., ensuring the zone admits non-trivial dynamics) but is not load-bearing in the classification theorem.

**Note.** This correction applies retroactively to the original Boolean SC. The same argument works for V = {⊤, ⊥}: the adversary adds admissible diagonal demanding ⊤, but diagonal-compatibility requires ⊤ = v for any existing demand v, which forces agreement. S* was unnecessary in v1.0 as well.

---

## 14. Summary

### Diagonal Semantics

$$\text{demand}(\text{diag}(\sigma) \text{ at level } k \text{ targeting } q) := \sigma(\alpha_{\leq k}(q))$$

| Diagonal Type | Condition | α_{≤k}(q) | Demand | Feas |
|---------------|-----------|-----------|--------|------|
| Admissible | ℓ(c) < ℓ(q) | e | σ(e) | {σ(e)} |
| Same-level | ℓ(c) = ℓ(q) | α(q) | σ(α(q)) | Fix(σ) |
| Downward | ℓ(c) > ℓ(q) | α^{(k)}(q) | σ(α^{(k)}(q)) | Fix(σ) |

### Definitions

| Term | Definition |
|------|------------|
| Coordinate level | ℓ(u,v,i) = max(ℓ(u), ℓ(v)) |
| Stratified | ∀c : ℓ(c) ≤ ℓ(target(c)) |
| Admissible diagonal | ℓ(c) < ℓ(target(c)) |
| Diagonal-compatible | All admissible diags at q agree on σ(e); agree with any target(t) |
| Target-consistent | No coordinate has target(t₁) and target(t₂) with t₁ ≠ t₂ |
| Conflict-free | Inductive: diam(Demands(q)) = 0 at each level |
| Coherent | Sol(ℱ) ≠ ∅ |
| Determined | Sol(ℱ) = {α} |
| Robustly determined | Determined under (D', E)-extensions |

### Theorems

| Name | Statement |
|------|-----------|
| Non-Admissible Classification (4.1) | Fix(σ) = ∅ ⟹ incoherent; {x\*} ⟹ forced; \|Fix\| > 1 ⟹ indeterminate |
| Admissible Demand (4.3) | Admissible diagonal demands σ(e) |
| No Intrinsic Lethality (9.1) | On connected V: κ ≥ 2 always |
| Helly Bound (9.2) | Convex Feas on V ⊆ ℝⁿ: κ ≤ n + 1 |
| Decomposition (6.1) | Under stratification: Sol ≅ conditioned product of CP_j |
| Determined Sufficiency (12.1) | 4 conditions ⟹ Sol = {α} |
| Pointwise Coherence (13.1) | Sol ≠ ∅ iff construction never encounters CP_j = ∅ |
| Robust Determination (13.2) | Robustly determined ⟺ admissible-only ∧ diagonal-compatible ∧ no couplings ∧ target-consistent |

### Proof Status

| Theorem | Tag | Notes |
|---------|-----|-------|
| 4.1 (Diagonal Classification) | [Structural] | Full case analysis |
| 6.1 (Decomposition) | [Structural] | Requires stratification |
| 9.1 (No Intrinsic Lethality) | [Derived] | Requires connected V |
| 9.2 (Helly Bound) | [Derived] | Requires convex Feas |
| 12.1 (Determined Sufficiency) | [Structural] | 4 conditions, full proof |
| 12.2 (General Sufficiency) | [Schema] | Depends on asserted 4', 5 |
| 13.1 (Pointwise Coherence) | [Structural] | From decomposition |
| 13.2 ⇐ (Sufficiency) | [Structural] | Chains from 12.1 |
| 13.2 ⇒ (Necessity) | [Structural] | All contrapositives proved |

### Conditions Removed from v1.0

| Condition | Why removed | Surviving role |
|-----------|-------------|----------------|
| Stratification (for non-diagonals) | Subsumed by admissible-only for diags; inert for non-diags in determination proofs | §4 prefix semantics only |
| S* (Global Separation) | Adversary blocked by diagonal-compatibility regardless; no counterexample exists | Richness condition on zone (optional) |

---

## Appendix A: Stratified Coherence in the Landscape of Diagonal Constraint Semantics

### A.1 Scope of the Core Theory

Stratified Coherence (SC), as presented in the main body, fixes a specific semantic regime: total valuations over a complete metric value space, persistent constraints, self-referential diagonal operators via continuous involutions, and stratification over a well-founded level structure. All theorems are proved within this regime.

### A.2 Diagonal Constraint Systems (Informal)

A **Diagonal Constraint System (DCS)** is any constraint-based semantic system equipped with an evaluation operator admitting fixed points, some form of diagonal or self-referential constraint, and a notion of coherence. SC corresponds to one stratum: the **total, persistent, self-threatening diagonal stratum**.

### A.3 Axes of Variation

**Valuation Regime**

| Regime | Description |
|--------|-------------|
| Total (SC) | Every coordinate must evaluate to some v ∈ V |
| Partial | Undefined values permitted (recovering Kripke-style fixed points) |
| Paraconsistent / many-valued | Conflicts tolerated without collapse |

**Value Space**

| Space | Description |
|-------|-------------|
| Boolean {⊤, ⊥} (SC v1.0) | Classical two-valued; Fix(¬) = ∅; all non-admissible diags lethal |
| [0, 1] (SC v2.0) | Continuous; Fix(σ) ≠ ∅ by IVT; no intrinsic lethality |
| General (V, d) (SC v2.0) | Complete metric; lethality depends on topology of V |

**Diagonal Strength**

| Strength | Description |
|----------|-------------|
| Self-threatening (SC) | Diagonals may reference the value being defined |
| Grounded | Diagonals reference only strictly lower strata, eliminating diagonal lethality |
| Delayed / modal | Diagonals reference future or hypothetical stages |

**Persistence Discipline**

| Discipline | Description |
|------------|-------------|
| Monotone (SC) | Constraints, once added, remain |
| Retractable | Constraints may be withdrawn or revised |
| Versioned | Constraints evolve across explicit stages |

### A.4 Relationship to Existing Work

Dropping totality while retaining diagonal self-reference recovers **Kripke's partial fixed-point semantics**.

Grounding diagonal operators collapses SC to a **stratified evaluation scheme** resembling Horn-style or acyclic constraint propagation, in which S* and robustness analysis become unnecessary.

The admissibility condition (ℓ(c) < ℓ(target(c))) is structurally identical to **guarded recursion** (Nakano 2000). SC's contribution is the classification-theoretic consequences under total semantics.

### A.5 Open Problems

**Relaxed diagonal compatibility.** Determine whether diagonal-compatibility can be weakened without reintroducing incoherence under admissible extensions.

**Finite vs transfinite stratification.** Analyze whether the classification theorems change when L is finite or bounded.

**Mode structure.** For mode-coherent systems (μ > 0), characterize the geometry of Sol(ℱ). When does the mode manifold have additional structure (e.g., group action, symplectic form)?

**Coupled component feasibility.** Derive structural conditions under which CP_j^W ≠ ∅, closing the gap between Theorem 12.1 [Structural] and Theorem 12.2 [Schema].

### A.6 Positioning

SC isolates and fully characterizes one semantic regime, proving that within it, coherence is sharply constrained by four structural conditions. It serves both as a complete theory and as a foundation for broader study of diagonal constraint semantics over general value spaces.

---

## References

Brouwer, L. E. J. (1911). Über Abbildung von Mannigfaltigkeiten. *Mathematische Annalen*, 71(1), 97–115.

Helly, E. (1923). Über Mengen konvexer Körper mit gemeinschaftlichen Punkten. *Jahresbericht der Deutschen Mathematiker-Vereinigung*, 32, 175–176.

Kripke, S. (1975). Outline of a theory of truth. *Journal of Philosophy*, 72(19), 690–716.

Nakano, H. (2000). A modality for recursion. *Proceedings of the 15th Annual IEEE Symposium on Logic in Computer Science (LICS)*, 255–266.

Tarski, A. (1936). The concept of truth in formalized languages. In *Logic, Semantics, Metamathematics*, 152–278. Oxford University Press (1956 translation).
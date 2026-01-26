# REPO: the umbrella concept for this project

## Intuition and motivation
This atom is not a mathematical statement at all. It is the idea that *this repository itself* is a structured, two-track explanation of one proof. The goal is to make a deep theorem accessible in two complementary ways:

- a human-readable lecture note (LaTeX), and
- a machine-checkable proof (Lean).

Think of it like a project that ships both a **textbook** and a **compiler-verified blueprint** of the same construction. The REPO atom exists so the rest of the atoms have a home: it tells you what the project is, why it exists, and how the different parts line up.

## What REPO represents (from `history/breakdown.md`)
- **Represents:** The repository itself as a coherent proof project: LaTeX lecture notes plus Lean formalization of the Sensitivity Conjecture proof.
- **Depends on:** Nothing. It is a top-level umbrella, not a math claim.
- **What depends on it:**
  - **GOAL** (the final theorem statement),
  - **INF_LEAN** (Lean scaffolding / setup),
  - **INF_TEX** (LaTeX scaffolding / narrative).

In the dependency graph, REPO is the root node that lets you understand *why* the other nodes exist.

## Plain-language picture
Imagine you want to be confident in a complicated proof:

- **Lecture notes** help humans follow the story and intuition.
- **Formal proofs** force every step to be correct.
- **A concept map** helps keep track of all the pieces.

This repository intentionally contains all three. REPO is the label for that design.

## What lives inside the repo (concrete anchors)
### 1) Human exposition: `sensitivity-polynomial.tex`
The LaTeX file is a lecture-style narrative. The abstract sets the main claim:

```tex
\begin{abstract}
Presenting \cite{Huang19}. A boolean function of degree $n$ has sensitivity at least $\sqrt n$.
\end{abstract}
```

In plain language: if a Boolean function depends on high-degree interactions among variables, it must be sensitive to flipping inputs in a noticeable way. This is the core mathematical story the repo is about.

### 2) Formal proof: `sensitivity.lean`
The Lean file is a fully formalized version of the same proof. It even states the central theorem in code:

```lean
/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
  classical
  -- Reduce to any level set with the "right" adjacency-count equality.
  ...
```

If you have never used Lean, you can read this as:
> For any Boolean function on `n` bits, if its polynomial degree is `n`, then its sensitivity is at least `sqrt(n)`.

The rest of the file is the formal proof of that statement and the reduction to the general case.

### 3) Concept map: `history/breakdown.md`
This file breaks the proof into small “atoms.” REPO is the topmost one and says: *this project is about proving the Sensitivity Conjecture in both LaTeX and Lean*. Every other atom is a piece of that proof.

## How REPO connects to neighboring atoms
- **REPO → GOAL:** The repo is organized around the final theorem goal. Without the project context, the goal is just a floating statement.
- **REPO → INF_TEX:** The repo includes a narrative explanation. INF_TEX is the scaffolding that makes the lecture note readable (packages, macros, structure).
- **REPO → INF_LEAN:** The repo also includes a formal proof. INF_LEAN is the scaffolding that makes the Lean file compile (imports, options, custom tactics).

So REPO tells you, “this is a two-track proof project,” and the neighboring atoms tell you *how* each track is built.

## Prerequisites (minimal)
You do not need formal math or Lean experience to grasp REPO. The only background ideas worth knowing are:
- **What a repository is:** a folder that collects related files for a project.
- **What LaTeX is:** a typesetting system for math-heavy documents.
- **What Lean is:** a proof assistant that checks formal proofs.

If you want to understand the math itself, you would next look at:
- **GOAL** (the final theorem statement), and
- the definitions of **sensitivity** and **degree** (atoms **SEN0** and **DEG0**).

## Why this atom matters
REPO is the “table of contents” idea. It tells you the proof is being built twice: once for humans, once for machines. That dual structure is what makes the rest of the atoms meaningful and navigable.

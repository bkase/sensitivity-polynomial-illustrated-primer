# INF_TEX: the LaTeX scaffolding + narrative layer

## Intuition and motivation
When a proof is formalized in Lean, it is precise but not friendly for most readers. INF_TEX is the human-facing mirror: it is the LaTeX lecture notes that explain the same proof in words, pictures, and familiar math notation. Think of it as the "guidebook" that sits next to the formal machine-checked proof. It does not add new mathematics; it makes the existing mathematics readable and teachable.

An analogy: if the Lean file is the executable blueprint, INF_TEX is the illustrated manual. You can build the same house from either, but only one is meant for humans to learn from.

## What INF_TEX represents
INF_TEX corresponds to the LaTeX file `sensitivity-polynomial.tex`. It contains:
- Preamble scaffolding (packages, macros, theorem environments) so notation is consistent and readable.
- Narrative sections that walk through the proof in a lecture-note style.
- Occasional placeholders for figures (TikZ) and informal explanations that would be out of place in a formal proof assistant.

So INF_TEX is a presentation layer, not a mathematical dependency. It is a "view" of the proof, not a building block.

## Dependencies and downstream links (from breakdown.md)
**Depends on:**
- **CHI0**: parity characters `chi_S` are defined and used early.
- **MINMAX**: the Courant-Fischer min-max principle appears in the interlacing section.
- **HUANG_DEF**: the Huang matrix `A_n` is defined and used in the spectral argument.
- **FULLCASE**: the full-degree sensitivity lower bound is stated as the main theorem.

**What depends on INF_TEX:**
- No mathematical atoms depend on INF_TEX. It is purely explanatory. The formal proof and all math dependencies stand without it.

## How INF_TEX connects to neighboring concepts
INF_TEX is a narrative walkthrough of the same chain of ideas that the Lean file formalizes:
- **CHI0 (parity characters)** shows up in the "Fourier analysis" section as the basis functions. From the LaTeX file:
  ```latex
  A function $f : 2^n \rightarrow 2$ is called a boolean function. We will often use $S, x$ interchangeably for vectors/sets of indices from $[n]$. Define $\chi_S(x) := (-1)^{x \cdot S}$.
  ```
  In Lean, this is formalized as:
  ```lean
  def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
    if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1
  ```

- **MINMAX (Courant-Fischer)** appears in the "Cauchy interlace" section. From the LaTeX file:
  ```latex
  \begin{lemma}\label{cauchy}
      If $A$ has real eigenvalues (or is Hermitian?) then the $k^{th}$ eigenvalue is given by
  \[
      \lambda_k = \max_C \min_{\norm{x} = 1, x \in C} \langle Ax, x \rangle
  \]
  where $C$ is any $k$-dimensional subspace.
  \end{lemma}
  ```
  The notes explain this geometrically, with a picture placeholder, to motivate interlacing.

- **HUANG_DEF (Huang matrix)** is introduced in the "Sensitivity"/"Lemmas" section. From the LaTeX file:
  ```latex
  \begin{align}
      A_1 = B_1 &:=
          \begin{pmatrix}
          0 & 1 \\
          1 & 0
          \end{pmatrix} &
      A_{n+1} &:= \begin{pmatrix}
          A_n & I_{2^n} \\
          I_{2^n} & -A_n
          \end{pmatrix} &
      B_{n+1} &:= \begin{pmatrix}
          B_n & I_{2^n} \\
          I_{2^n} & B_n
          \end{pmatrix}
  \end{align}
  ```
  In Lean, this is formalized as:
  ```lean
  def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
    match n with
    | 0 => 0
    | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
        (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))
  ```

- **FULLCASE (main full-degree theorem)** is stated in the "Main proof" section. From the LaTeX file:
  ```latex
  \begin{theorem}
      $|s(f)| \ge \sqrt {\deg(f)}$.
  \end{theorem}
  ```
  In Lean, this is formalized as:
  ```lean
  theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
    (sensitivity f : ℝ) ≥ Real.sqrt n
  ```
  And the general statement:
  ```lean
  theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (sensitivity f : ℝ) ≥ Real.sqrt (degree f)
  ```

## What the "scaffolding" looks like
The preamble defines notation and theorem environments so later sections stay readable. From the LaTeX file:
```latex
\usepackage{amsthm, amsmath, amssymb, array, float, stackengine, appendix}
\usepackage{tikz}
\usepackage{mathtools}
\usepackage{listings}
\usepackage{color}
\usepackage{hyperref}

% Math commands
\newcommand{\sups}[1]{\ensuremath{^{\textrm{#1}}}}
\newcommand{\subs}[1]{\ensuremath{_{\textrm{#1}}}}
\newcommand{\mono}[1]{$\mathcal{M}_{#1}$}
\newcommand{\EE}{\mathbb{E}}
\newcommand{\FF}{\mathbb{F}}
\newcommand{\NN}{\mathbb{N}}
\newcommand{\PP}{\mathbb{P}}
\newcommand{\pcal}{\mathcal P}
\newcommand{\RR}{\mathbb{R}}
\newcommand{\ZZ}{\mathbb{Z}}
\newcommand{\two}{\left\{0, 1\right\}}
\newcommand{\pred}{\mathcal{P}}
\newcommand{\acz}{\text{AC}^0}
\newcommand{\norm}[1]{\left\lVert#1\right\rVert}

% Theorem environments
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}
\newtheorem{Col}{Corollary}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{proposition}{Proposition}
\newtheorem{conjecture}{Conjecture}
\newtheorem{claim}{Claim}
```
This is not math content; it is the formatting infrastructure that keeps symbols and theorem statements consistent.

## A small example of narrative glue
The notes use informal explanation to connect steps that are formalized in Lean. For instance, the sensitivity section introduces a parity-flipped function and a large level set. From the LaTeX file:
```latex
We can start to look at this as a graph and write $x \sim y$ if they differ in only 1 bit. We call this graph $Q_n$.
\[
s(f) := \max_{x} |\{y \mid x \sim y, f(x) \neq y\}|
\]
It is also helpful to have $\deg(f) = n$. To do this, pick a term $T$ in $f$ of maximum degree and restrict to the subcube $Q_T$. Now we have a simple problem on the graph above by flipping the value of $f$ by the parity of $x$ and looking for places where neighboring vertices get the same value. I.e., let $g(x) := f(x) \chi_{[n]}$. Then we can let $S := \{x \mid g(x) = 1\}$ and sensitivity becomes simply
\[
s(f) = \max(d_S(g), d_{Q_n \setminus S}(g))
\]
```
In Lean, the sensitivity definition is:
```lean
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x => Finset.card (Finset.filter (fun y => (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y) Finset.univ))
```
This is the kind of connective tissue INF_TEX provides.

## Summary of INF_TEX in one sentence
INF_TEX is the LaTeX lecture-note layer (`sensitivity-polynomial.tex`) that packages the same proof into readable exposition, with macros, sections, and intuition, while relying on the underlying mathematical atoms (CHI0, MINMAX, HUANG_DEF, FULLCASE) and feeding nothing back into them.

## Prerequisite pointers (if you want to go deeper)
- **CHI0:** what parity characters are and why they form a basis.
- **MINMAX:** how the Courant-Fischer principle gives interlacing.
- **HUANG_DEF:** how the recursive matrix `A_n` is constructed.
- **FULLCASE:** the full-degree sensitivity lower bound statement.

If you want the formal version, the Lean file `sensitivity.lean` is the machine-checked counterpart; INF_TEX is the human story.

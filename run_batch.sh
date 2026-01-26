#!/bin/bash

cd /Users/bkase/Documents/papers/sensitivity-polynomial/illustrated-primer

ATOM=$1

PROMPT="You are explaining the concept '$ATOM' from a mathematical proof about the Sensitivity Conjecture.

First, read these files to understand the context:
1. sensitivity-polynomial.tex - the LaTeX lecture notes
2. sensitivity.lean - the Lean formalization
3. history/breakdown.md - describes each 'atom' (conceptual chunk) of the proof

Focus on the atom named '$ATOM'. According to breakdown.md, find what this atom represents, what it depends on, and what depends on it.

Then write a thorough, accessible explanation of '$ATOM' in output/${ATOM}.md for someone who:
- Is vaguely technical and interested in math
- Does NOT have formal math training
- Does NOT have Lean/proof assistant experience

The explanation should:
- Start with intuition and motivation (why do we need this?)
- Explain the concept in plain language with analogies
- Show how it connects to neighboring concepts in the proof
- Include relevant code/math snippets with explanations
- Be self-contained but reference prerequisites

Write the complete explanation to output/${ATOM}.md"

codex --full-auto "$PROMPT"

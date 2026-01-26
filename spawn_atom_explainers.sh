#!/bin/bash

cd /Users/bkase/Documents/papers/sensitivity-polynomial/illustrated-primer

ATOMS=(
  "REPO"
  "GOAL"
  "FULLCASE"
  "REDUCE"
  "INF_LEAN"
  "AUX"
  "INF_TEX"
  "BC0"
  "BC1"
  "BC2"
  "BC3"
  "BC4"
  "SEN0"
  "CHI0"
  "FOURIER0"
  "DEG0"
  "FULLCOEF"
  "DEG_WITNESS"
  "RESTRICT0"
  "SENS_MONO"
  "FOURIER_AVG"
  "EXIST_TOP"
  "DEG_FROM_TOP"
  "GVAL0"
  "LEVELSETS"
  "NEIGH_PARITY"
  "NEIGH_RULE"
  "DEG_SENS_LEVEL"
  "HUANG_DEF"
  "HUANG_PROP"
  "HUANG_SPEC"
  "ABS_ADJ"
  "HUANG_REIDX"
  "SUBMAT"
  "IND_GRAPH"
  "SUBMAT_BOUND"
  "ROWSUM_BOUND"
  "SPEC_UPPER"
  "RAYLEIGH"
  "MINMAX"
  "INTERLACE"
  "HUANG_SUB_LOWER"
  "GRAPH_ISO"
)

SESSION="atom_explainers"

for i in "${!ATOMS[@]}"; do
  ATOM="${ATOMS[$i]}"

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

  if [ $i -eq 0 ]; then
    # First window already exists, just rename and run
    tmux rename-window -t "$SESSION:0" "$ATOM"
    tmux send-keys -t "$SESSION:0" "cd /Users/bkase/Documents/papers/sensitivity-polynomial/illustrated-primer && codex --full-auto \"$PROMPT\"" Enter
  else
    # Create new window
    tmux new-window -t "$SESSION" -n "$ATOM"
    tmux send-keys -t "$SESSION:$ATOM" "cd /Users/bkase/Documents/papers/sensitivity-polynomial/illustrated-primer && codex --full-auto \"$PROMPT\"" Enter
  fi

  # Delay between spawns to avoid overwhelming the system
  sleep 2
done

echo "Spawned ${#ATOMS[@]} codex instances in tmux session '$SESSION'"
echo "Attach with: tmux attach -t $SESSION"

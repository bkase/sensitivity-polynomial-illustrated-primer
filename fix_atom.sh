#!/bin/bash

cd /Users/bkase/Documents/papers/sensitivity-polynomial/illustrated-primer

ATOM=$1

PROMPT="You need to fix the explanation file output/${ATOM}.md to use VERBATIM Lean code from sensitivity.lean.

CRITICAL REQUIREMENTS:
1. First, read sensitivity.lean to find ALL Lean code relevant to the atom '$ATOM'
2. Read the current output/${ATOM}.md file
3. Replace ANY Lean code blocks in the markdown with the EXACT, VERBATIM code from sensitivity.lean
4. Do NOT paraphrase, simplify, or modify the Lean code in any way - copy it exactly as it appears
5. Keep the prose explanations but update them to match the actual code
6. If the explanation references definitions/theorems that exist in the Lean file, quote them exactly

For example, if the explanation has:
\`\`\`lean
def foo (n : Nat) := n + 1
\`\`\`

But the actual sensitivity.lean has:
\`\`\`lean
def foo (n : ℕ) : ℕ := n + 1
\`\`\`

You MUST replace with the exact version from sensitivity.lean.

Read sensitivity.lean first, then fix output/${ATOM}.md to use verbatim code from it.
Write the corrected explanation back to output/${ATOM}.md"

codex --full-auto "$PROMPT"

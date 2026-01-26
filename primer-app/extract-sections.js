// Extract code sections from frontend.tsx for Codex explanations
const fs = require('fs');

const frontendPath = './src/frontend.tsx';
const content = fs.readFileSync(frontendPath, 'utf-8');

// Find the fullLeanCode template literal
const startMarker = 'const fullLeanCode = `';
const endMarker = '`;';

const startIdx = content.indexOf(startMarker);
if (startIdx === -1) {
  console.error('Could not find fullLeanCode');
  process.exit(1);
}

const codeStart = startIdx + startMarker.length;
const codeEnd = content.indexOf(endMarker, codeStart);
const fullLeanCode = content.substring(codeStart, codeEnd);

const lines = fullLeanCode.split('\n');
console.log(`Total lines in fullLeanCode: ${lines.length}`);

// Section line ranges (from sectionLineRanges in frontend.tsx)
const sectionLineRanges = [
  [0, 10],     // 1. imports
  [11, 21],    // 2. sensitivity
  [22, 28],    // 3. chi
  [29, 41],    // 4. fourier/degree
  [42, 65],    // 5. equivalences
  [66, 79],    // 6. huang matrix def
  [80, 98],    // 7. huang_matrix_sq
  [99, 115],   // 8. eigenvalues
  [116, 149],  // 9. sorted eigenvalues
  [150, 159],  // 10. interlacing
  [160, 177],  // 11. g_expectation
  [178, 189],  // 12. huang_fin
  [190, 240],  // 13. symmetry
  [241, 279],  // 14. spectrum-theorem
  [280, 291],  // 15. spectral-bound
  [292, 299],  // 16. level-sets
  [300, 307],  // 17. hypercube-graph
  [308, 315],  // 18. chi-neighbor
  [316, 325],  // 19. g-neighbor
  [326, 338],  // 20. degree-sensitivity
  [339, 352],  // 21. full-degree-theorem
  [353, 359],  // 22. restriction
  [360, 367],  // 23. sensitivity-mono
  [368, 380],  // 24. conjecture
];

const sectionNames = [
  "Imports & Setup",
  "Sensitivity Definition",
  "Parity Character χ",
  "Fourier Coefficients & Degree",
  "Index Equivalences",
  "Huang Matrix Definition",
  "A² = nI",
  "Eigenvalue Characterization",
  "Sorted Eigenvalues Infrastructure",
  "Inner Product Symmetry",
  "g-Transform Expectation",
  "Reindexed Huang Matrix",
  "Symmetry & Trace Theorems",
  "Complete Spectrum",
  "g-Value and Level Sets",
  "Large Level Set Existence",
  "Hypercube Graph Definition",
  "Parity Flip on Edges",
  "g-Transform Neighbor Property",
  "Degree = Sensitivity in Level Sets",
  "Full-Degree Theorem",
  "Restriction to Subcubes",
  "Sensitivity Monotonicity",
  "The Sensitivity Conjecture"
];

// Extract and save each section
for (let i = 0; i < sectionLineRanges.length; i++) {
  const [start, end] = sectionLineRanges[i];
  const sectionLines = lines.slice(start, end + 1);
  const sectionCode = sectionLines.join('\n');

  const outPath = `/tmp/lean-sections/section-${i + 1}.lean`;
  fs.writeFileSync(outPath, sectionCode);
  console.log(`Section ${i + 1} (${sectionNames[i]}): lines ${start}-${end}, ${sectionLines.length} lines -> ${outPath}`);
}

console.log('\nExtraction complete!');

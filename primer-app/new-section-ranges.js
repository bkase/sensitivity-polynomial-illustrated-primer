// Generate new section ranges for the full 1936-line Lean code
const fs = require('fs');

// Based on the key definition locations found:
// The code structure is:
// 0-206: Harmonic.GeneralizeProofs tactic (meta-level, can be one "infrastructure" section)
// 207-231: set_option declarations
// 232-236: noncomputable section + blank
// 237-242: def sensitivity
// 243-248: def chi
// 249-256: fourier_coeff and degree
// 258-289: equivalences (boolProdEquivSum, finSuccEquiv_custom, finSuccEquiv_huang_custom)
// 291-298: def huang_matrix
// 300-316: theorem huang_matrix_sq
// 318-331: theorem huang_matrix_eigenvalues
// 334-365: sorted eigenvalues infrastructure (sorted_eigenvalues_list, interlacing, isSymm_iff_isHermitian, sorted_eigenvalues)
// 370-379: dotProduct_mulVec_symm
// 381-530: min_max_eigenvalue and spectral theory (a big section)
// 532-543: g_expectation_nonzero
// 545-575: boolFunEquivFin, huang_matrix_fin, huang_matrix_isSymm, huang_matrix_fin_isSymm
// 576-600: huang_matrix_fin_sq, huang_matrix_trace
// 602-822: huang_eigenvalues_sq_eq_n and related lemmas
// 823-877: abs_huang_eq_adjacency
// 878-910: eigenvalue_le_max_row_sum
// 911-937: spectral_radius_bound
// 939-1277: rayleigh_quotient and Courant-Fischer theory
// 1278-1356: eigenvalue_interlacing_max
// 1357-1387: huang_submatrix_max_eigenvalue_ge_sqrt_n
// 1388-1420: g_val, S_pos, S_neg definitions
// 1421-1465: S_pos_union_S_neg, S_pos_disjoint_S_neg, exists_large_level_set
// 1466-1806: hypercube_graph and graph theory lemmas
// 1807-1815: def restriction
// 1816-1904: sensitivity_restriction_le and related
// 1905-1935: sensitivity_conjecture (FINAL)

// New section line ranges for 24 sections
const newSectionLineRanges = [
  [0, 206],       // 1. Harmonic Tactic Infrastructure
  [207, 236],     // 2. Imports & Setup (set_option, noncomputable)
  [237, 242],     // 3. Sensitivity Definition
  [243, 248],     // 4. Parity Character χ
  [249, 257],     // 5. Fourier Coefficients & Degree
  [258, 290],     // 6. Index Equivalences
  [291, 299],     // 7. Huang Matrix Definition
  [300, 317],     // 8. A² = nI
  [318, 333],     // 9. Eigenvalue Characterization
  [334, 380],     // 10. Sorted Eigenvalues Infrastructure
  [381, 531],     // 11. Min-Max Eigenvalue & Spectral Theory
  [532, 544],     // 12. g-Transform Expectation
  [545, 601],     // 13. Reindexed Huang Matrix & Symmetry
  [602, 822],     // 14. Huang Eigenvalues Complete Spectrum
  [823, 910],     // 15. Adjacency & Row Sum Bounds
  [911, 938],     // 16. Spectral Radius Bound
  [939, 1277],    // 17. Rayleigh Quotient & Courant-Fischer
  [1278, 1356],   // 18. Eigenvalue Interlacing
  [1357, 1387],   // 19. Huang Submatrix Eigenvalue Bound
  [1388, 1442],   // 20. g-Value and Level Sets
  [1443, 1465],   // 21. Large Level Set Existence
  [1466, 1806],   // 22. Hypercube Graph & Properties
  [1807, 1904],   // 23. Restriction & Sensitivity Monotonicity
  [1905, 1935],   // 24. The Sensitivity Conjecture
];

const newSectionNames = [
  "Harmonic Tactic Infrastructure",
  "Imports & Setup",
  "Sensitivity Definition",
  "Parity Character χ",
  "Fourier Coefficients & Degree",
  "Index Equivalences",
  "Huang Matrix Definition",
  "A² = nI",
  "Eigenvalue Characterization",
  "Sorted Eigenvalues Infrastructure",
  "Min-Max Eigenvalue & Spectral Theory",
  "g-Transform Expectation",
  "Reindexed Huang Matrix & Symmetry",
  "Huang Eigenvalues Complete Spectrum",
  "Adjacency & Row Sum Bounds",
  "Spectral Radius Bound",
  "Rayleigh Quotient & Courant-Fischer",
  "Eigenvalue Interlacing",
  "Huang Submatrix Eigenvalue Bound",
  "g-Value and Level Sets",
  "Large Level Set Existence",
  "Hypercube Graph & Properties",
  "Restriction & Sensitivity Monotonicity",
  "The Sensitivity Conjecture"
];

// Output the new ranges
console.log('New Section Line Ranges:');
console.log('========================');
for (let i = 0; i < newSectionLineRanges.length; i++) {
  const [start, end] = newSectionLineRanges[i];
  console.log(`  [${start}, ${end}],    // ${i + 1}. ${newSectionNames[i]}`);
}

console.log('\n\nSection Names Array:');
console.log('====================');
newSectionNames.forEach((name, i) => {
  console.log(`  "${name}",`);
});

// Now extract the sections to temp files
const frontendPath = './src/frontend.tsx';
const content = fs.readFileSync(frontendPath, 'utf-8');
const startMarker = 'const fullLeanCode = `';
const endMarker = '`;';
const startIdx = content.indexOf(startMarker);
const codeStart = startIdx + startMarker.length;
const codeEnd = content.indexOf(endMarker, codeStart);
const fullLeanCode = content.substring(codeStart, codeEnd);
const lines = fullLeanCode.split('\n');

console.log('\n\nExtracting sections to /tmp/lean-sections-new/...');
fs.mkdirSync('/tmp/lean-sections-new', { recursive: true });

for (let i = 0; i < newSectionLineRanges.length; i++) {
  const [start, end] = newSectionLineRanges[i];
  const sectionLines = lines.slice(start, end + 1);
  const sectionCode = sectionLines.join('\n');
  const outPath = `/tmp/lean-sections-new/section-${i + 1}.lean`;
  fs.writeFileSync(outPath, sectionCode);
  console.log(`Section ${i + 1} (${newSectionNames[i]}): lines ${start}-${end}, ${sectionLines.length} lines`);
}

console.log('\nDone!');

// Find key definitions in fullLeanCode to determine correct section ranges
const fs = require('fs');

const frontendPath = './src/frontend.tsx';
const content = fs.readFileSync(frontendPath, 'utf-8');

const startMarker = 'const fullLeanCode = `';
const endMarker = '`;';
const startIdx = content.indexOf(startMarker);
const codeStart = startIdx + startMarker.length;
const codeEnd = content.indexOf(endMarker, codeStart);
const fullLeanCode = content.substring(codeStart, codeEnd);

const lines = fullLeanCode.split('\n');
console.log(`Total lines: ${lines.length}\n`);

// Find key patterns
const patterns = [
  'def sensitivity',
  'def chi',
  'def fourier_coeff',
  'def degree',
  'def boolProdEquivSum',
  'def finSuccEquiv_custom',
  'def finSuccEquiv_huang',
  'def huang_matrix',
  'theorem huang_matrix_sq',
  'theorem huang_matrix_eigenvalues',
  'def sorted_eigenvalues_list',
  'def interlacing',
  'theorem isSymm_iff_isHermitian',
  'def sorted_eigenvalues',
  'theorem sorted_eigenvalues_length',
  'theorem dotProduct_mulVec_symm',
  'def min_max_eigenvalue',
  'theorem g_expectation_nonzero',
  'def boolFunEquivFin',
  'def huang_matrix_fin',
  'theorem huang_matrix_isSymm',
  'theorem huang_matrix_fin_isSymm',
  'theorem huang_matrix_fin_sq',
  'theorem huang_matrix_trace',
  'theorem huang_eigenvalues_sq_eq_n',
  'def g_val',
  'def S_pos',
  'def S_neg',
  'lemma exists_large_level_set',
  'def hypercube_graph',
  'theorem abs_huang_eq_adjacency',
  'theorem eigenvalue_le_max_row_sum',
  'theorem spectral_radius_bound',
  'def rayleigh_quotient',
  'lemma eigenvalue_interlacing',
  'lemma huang_submatrix_max_eigenvalue',
  'def restriction',
  'lemma sensitivity_restriction_le',
  'theorem sensitivity_conjecture',
  'noncomputable section',
  'end Harmonic',
  'set_option maxHeartbeats'
];

console.log('Key definition locations:');
console.log('=========================');

for (const pattern of patterns) {
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].includes(pattern)) {
      console.log(`Line ${i}: ${lines[i].trim().substring(0, 80)}`);
      break;
    }
  }
}

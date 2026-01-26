// Parse Codex outputs and extract the explanation content
const fs = require('fs');
const path = require('path');

const outputDir = '/tmp/codex-outputs';

// Map section numbers to their output files
const sectionFiles = {
  1: 'section-1-output.txt',
  2: 'pane-2-output.txt',  // Imports & Setup
  3: 'pane-3-output.txt',  // Sensitivity Definition
  4: 'pane-4-output.txt',  // Parity Character χ
  5: 'pane-2-output.txt',  // Fourier (from same pane, need to check)
  6: 'section-6-output.txt',
  7: 'section-7-output.txt',
  8: 'section-8-output.txt',
  9: 'section-9-output.txt',
  10: 'section-10-output.txt',
  11: 'section-11-output.txt',
  12: 'section-12-output.txt',
  13: 'section-13-output.txt',
  14: 'section-14-output.txt',
  15: 'section-15-output.txt',
  16: 'section-16-output.txt',
  17: 'section-17-output.txt',
  18: 'section-18-output.txt',
  19: 'section-19-output.txt',
  20: 'section-20-output.txt',
  21: 'section-21-output.txt',
  22: 'section-22-output.txt',
  23: 'section-23-output.txt',
  24: 'section-24-output.txt',
};

// Extract explanation text from Codex output (between "Worked for" and the next prompt)
function extractExplanation(content) {
  // Look for the pattern: "─ Worked for Xs ─" followed by the explanation
  const workedMatch = content.match(/─ Worked for \d+s ─+\n\n([\s\S]*?)(?=\n›|\nToken usage:|$)/);
  if (workedMatch) {
    return workedMatch[1].trim();
  }

  // Alternative: look for bullet point sections
  const bulletMatch = content.match(/• ([\s\S]*?)(?=\n›|\nToken usage:|$)/g);
  if (bulletMatch && bulletMatch.length > 0) {
    return bulletMatch.map(m => m.replace(/^• /, '')).join('\n\n').trim();
  }

  return null;
}

console.log('Parsing Codex outputs...\n');

const summaries = {};

for (const [sectionNum, fileName] of Object.entries(sectionFiles)) {
  const filePath = path.join(outputDir, fileName);
  if (fs.existsSync(filePath)) {
    const content = fs.readFileSync(filePath, 'utf-8');
    const explanation = extractExplanation(content);
    if (explanation) {
      summaries[sectionNum] = {
        file: fileName,
        length: explanation.length,
        preview: explanation.substring(0, 200) + '...'
      };
      console.log(`Section ${sectionNum}: ${explanation.length} chars`);
    } else {
      console.log(`Section ${sectionNum}: Could not extract (file exists)`);
    }
  } else {
    console.log(`Section ${sectionNum}: File not found - ${fileName}`);
  }
}

console.log('\n\nWriting full explanations to /tmp/lean-explanations/...');
fs.mkdirSync('/tmp/lean-explanations', { recursive: true });

for (const [sectionNum, fileName] of Object.entries(sectionFiles)) {
  const filePath = path.join(outputDir, fileName);
  if (fs.existsSync(filePath)) {
    const content = fs.readFileSync(filePath, 'utf-8');
    const explanation = extractExplanation(content);
    if (explanation) {
      fs.writeFileSync(`/tmp/lean-explanations/section-${sectionNum}.md`, explanation);
    }
  }
}

console.log('Done!');

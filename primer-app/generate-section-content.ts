import { readdirSync, readFileSync, writeFileSync } from 'fs';

const sectionsDir = './src/sections';
const files = readdirSync(sectionsDir).filter(f => f.endsWith('.mdx')).sort((a, b) => {
  const numA = parseInt(a.replace('section-', '').replace('.mdx', ''));
  const numB = parseInt(b.replace('section-', '').replace('.mdx', ''));
  return numA - numB;
});

let output = `// Auto-generated MDX content for each section
// Each section contains the explanation for that part of the Lean proof

export const sectionContent: Record<number, string> = {};

`;

for (const file of files) {
  const num = parseInt(file.replace('section-', '').replace('.mdx', ''));
  const content = readFileSync(`${sectionsDir}/${file}`, 'utf-8');
  // Escape backslashes first (for LaTeX), then backticks and ${}
  const escaped = content.replace(/\\/g, '\\\\').replace(/`/g, '\\`').replace(/\$\{/g, '\\${');
  output += `sectionContent[${num}] = \`${escaped}\`;\n\n`;
}

output += `export default sectionContent;\n`;

writeFileSync('./src/sectionContent.ts', output);
console.log('Generated sectionContent.ts with inlined content');

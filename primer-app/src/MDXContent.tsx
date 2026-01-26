import React, { useEffect, useState, useMemo } from 'react';
import MarkdownIt from 'markdown-it';
import hljs from 'highlight.js/lib/core';
import lean from 'highlightjs-lean';

// Register Lean language with highlight.js
hljs.registerLanguage('lean', lean);
hljs.registerLanguage('lean4', lean);

declare global {
  interface Window {
    katex?: {
      renderToString: (tex: string, options?: { displayMode?: boolean; throwOnError?: boolean }) => string;
    };
  }
}

// Convert LaTeX math to rendered HTML before markdown processing
function renderMathFirst(content: string): string {
  if (typeof window === 'undefined' || !window.katex) {
    return content;
  }

  // Replace display math \[...\] with placeholder
  let result = content.replace(/\\\[([\s\S]*?)\\\]/g, (_, math) => {
    try {
      const rendered = window.katex!.renderToString(math.trim(), { displayMode: true, throwOnError: false });
      return `<div class="math-block my-4">${rendered}</div>`;
    } catch (e) {
      console.error('KaTeX display error:', e, math);
      return `<div class="text-red-500">[Math Error: ${math}]</div>`;
    }
  });

  // Replace inline math \(...\)
  result = result.replace(/\\\((.*?)\\\)/g, (_, math) => {
    try {
      return window.katex!.renderToString(math.trim(), { displayMode: false, throwOnError: false });
    } catch (e) {
      console.error('KaTeX inline error:', e, math);
      return `<span class="text-red-500">[Math Error: ${math}]</span>`;
    }
  });

  // Also handle $$ ... $$ (display math)
  result = result.replace(/\$\$([\s\S]*?)\$\$/g, (_, math) => {
    try {
      const rendered = window.katex!.renderToString(math.trim(), { displayMode: true, throwOnError: false });
      return `<div class="math-block my-4">${rendered}</div>`;
    } catch (e) {
      console.error('KaTeX display $$ error:', e, math);
      return `<div class="text-red-500">[Math Error: ${math}]</div>`;
    }
  });

  // Handle inline $...$ (but not $$)
  result = result.replace(/(?<!\$)\$(?!\$)([^\$\n]+?)\$(?!\$)/g, (_, math) => {
    try {
      return window.katex!.renderToString(math.trim(), { displayMode: false, throwOnError: false });
    } catch (e) {
      console.error('KaTeX inline $ error:', e, math);
      return `<span class="text-red-500">[Math Error: ${math}]</span>`;
    }
  });

  return result;
}

interface MDXContentProps {
  content: string;
  className?: string;
}

export function MDXContent({ content, className }: MDXContentProps) {
  const [katexReady, setKatexReady] = useState(false);

  useEffect(() => {
    // Check if KaTeX is loaded
    const checkKatex = () => {
      if (typeof window !== 'undefined' && window.katex) {
        setKatexReady(true);
        return true;
      }
      return false;
    };

    if (!checkKatex()) {
      // Poll for KaTeX
      const interval = setInterval(() => {
        if (checkKatex()) {
          clearInterval(interval);
        }
      }, 100);
      return () => clearInterval(interval);
    }
  }, []);

  const html = useMemo(() => {
    if (!katexReady) return '';

    // First render all math to HTML
    const withMath = renderMathFirst(content);

    const md = new MarkdownIt({
      html: true,  // Important: allow HTML pass-through
      linkify: true,
      typographer: true,
      highlight: function (str, lang) {
        // Try to highlight with the specified language or default to lean
        const language = lang || 'lean';
        if (hljs.getLanguage(language)) {
          try {
            return '<pre class="hljs"><code>' +
              hljs.highlight(str, { language, ignoreIllegals: true }).value +
              '</code></pre>';
          } catch (__) {}
        }
        // Fallback: escape HTML and return
        return '<pre class="hljs"><code>' + md.utils.escapeHtml(str) + '</code></pre>';
      }
    });

    // Render markdown (HTML from KaTeX will pass through)
    return md.render(withMath);
  }, [content, katexReady]);

  if (!katexReady) {
    return (
      <div className="text-stone-400 text-sm animate-pulse">
        Loading...
      </div>
    );
  }

  return (
    <div
      className={`mdx-content prose prose-stone prose-sm max-w-none ${className || ''}`}
      dangerouslySetInnerHTML={{ __html: html }}
    />
  );
}

export default MDXContent;

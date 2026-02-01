import React, { useState, useCallback, useMemo, useRef, useEffect } from "react";
import { createRoot } from "react-dom/client";
import * as THREE from "three";
import { OrbitControls } from "three/examples/jsm/controls/OrbitControls.js";
import "./index.css";
import { MDXContent } from "./MDXContent";
import sectionContent from "./sectionContent";

// ============================================================================
// TYPES & COLORS
// ============================================================================

type Section =
  | "intro"
  | "cube"
  | "sensitivity"
  | "fourier"
  | "gTransform"
  | "huang"
  | "spectral"
  | "proof"
  | "leanProof";

interface Vertex {
  bits: boolean[];
  label: string;
}

const COLORS = {
  primerGold: "#d4a574",
  primerGoldLight: "#f5e6d3",
  primerInk: "#2c1810",
  primerPaper: "#faf6f1",
  primerAccent: "#8b4513",
  cubeVertex: "#4a90d9",
  cubeEdge: "#6bb3f7",
  cubeActive: "#ff6b6b",
  cubePositive: "#51cf66",
  cubeNegative: "#ff6b6b",
  matrixPositive: "#51cf66",
  matrixNegative: "#ff6b6b",
  matrixZero: "#dee2e6",
};

// ============================================================================
// LATEX COMPONENT (uses KaTeX from CDN)
// ============================================================================

declare global {
  interface Window {
    katex: {
      render: (tex: string, element: HTMLElement, options?: object) => void;
      renderToString: (tex: string, options?: object) => string;
    };
  }
}

function Latex({ children, display = false }: { children: string; display?: boolean }) {
  const ref = useRef<HTMLSpanElement>(null);
  const [katexReady, setKatexReady] = useState(false);

  // Check if KaTeX is loaded, poll if not
  useEffect(() => {
    if (window.katex) {
      setKatexReady(true);
      return;
    }

    // Poll for KaTeX to be available
    const checkKatex = setInterval(() => {
      if (window.katex) {
        setKatexReady(true);
        clearInterval(checkKatex);
      }
    }, 50);

    return () => clearInterval(checkKatex);
  }, []);

  // Render when KaTeX is ready
  useEffect(() => {
    if (ref.current && katexReady && window.katex) {
      try {
        window.katex.render(children, ref.current, {
          displayMode: display,
          throwOnError: false,
        });
      } catch (e) {
        console.error("KaTeX error:", e);
        ref.current.textContent = children;
      }
    }
  }, [children, display, katexReady]);

  return <span ref={ref} className={display ? "block my-4 text-center" : "inline"} />;
}

// ============================================================================
// LEAN CODE COMPONENT
// ============================================================================

function LeanCode({ children, title }: { children: string; title?: string }) {
  return (
    <div className="my-6">
      {title && (
        <div className="bg-stone-700 text-stone-200 text-xs px-4 py-2 rounded-t-lg font-mono">
          {title}
        </div>
      )}
      <pre className={`bg-stone-800 text-stone-100 p-4 overflow-x-auto text-sm font-mono leading-relaxed ${title ? "rounded-b-lg" : "rounded-lg"}`}>
        <code>{children.trim()}</code>
      </pre>
    </div>
  );
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

function generateVertices(n: number): Vertex[] {
  const vertices: Vertex[] = [];
  for (let i = 0; i < (1 << n); i++) {
    const bits: boolean[] = [];
    for (let j = 0; j < n; j++) {
      bits.push(((i >> j) & 1) === 1);
    }
    vertices.push({
      bits,
      label: bits.map(b => b ? "1" : "0").join(""),
    });
  }
  return vertices;
}

function hammingDistance(a: boolean[], b: boolean[]): number {
  let dist = 0;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) dist++;
  }
  return dist;
}

function chi(S: number[], x: boolean[]): number {
  let count = 0;
  for (const i of S) {
    if (x[i]) count++;
  }
  return count % 2 === 0 ? 1 : -1;
}

// ============================================================================
// THREE.JS HYPERCUBE COMPONENT
// ============================================================================

function ThreeHypercube({
  n,
  highlightNeighbors = false,
  colorFunction,
  onVertexSelect,
  selectedVertex,
}: {
  n: number;
  highlightNeighbors?: boolean;
  colorFunction?: (bits: boolean[]) => string;
  onVertexSelect?: (idx: number | null) => void;
  selectedVertex?: number | null;
}) {
  const containerRef = useRef<HTMLDivElement>(null);
  const sceneRef = useRef<THREE.Scene | null>(null);
  const rendererRef = useRef<THREE.WebGLRenderer | null>(null);
  const cameraRef = useRef<THREE.PerspectiveCamera | null>(null);
  const controlsRef = useRef<OrbitControls | null>(null);
  const vertexMeshesRef = useRef<THREE.Mesh[]>([]);
  const edgeLinesRef = useRef<THREE.Line[]>([]);
  const animationRef = useRef<number>(0);

  const vertices = useMemo(() => generateVertices(n), [n]);

  const getPosition3D = useCallback((bits: boolean[]): THREE.Vector3 => {
    const scale = 1.5;
    if (n === 2) {
      return new THREE.Vector3(
        (bits[0] ? 1 : -1) * scale,
        (bits[1] ? 1 : -1) * scale,
        0
      );
    } else if (n === 3) {
      return new THREE.Vector3(
        (bits[0] ? 1 : -1) * scale,
        (bits[1] ? 1 : -1) * scale,
        (bits[2] ? 1 : -1) * scale
      );
    }
    // For higher dimensions, project to 3D
    let x = 0, y = 0, z = 0;
    for (let i = 0; i < bits.length; i++) {
      const angle = (i / bits.length) * Math.PI * 2;
      const val = bits[i] ? 1 : -1;
      x += Math.cos(angle) * val * 0.5;
      y += Math.sin(angle) * val * 0.5;
      z += (i % 2 === 0 ? 1 : -1) * val * 0.3;
    }
    return new THREE.Vector3(x * scale, y * scale, z * scale);
  }, [n]);

  useEffect(() => {
    if (!containerRef.current) return;

    // Setup scene
    const scene = new THREE.Scene();
    scene.background = new THREE.Color(COLORS.primerPaper);
    sceneRef.current = scene;

    // Setup camera
    const camera = new THREE.PerspectiveCamera(50, 1, 0.1, 100);
    camera.position.set(4, 3, 4);
    cameraRef.current = camera;

    // Setup renderer
    const renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setSize(300, 300);
    renderer.setPixelRatio(window.devicePixelRatio);
    containerRef.current.appendChild(renderer.domElement);
    rendererRef.current = renderer;

    // Setup controls
    const controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.05;
    controls.autoRotate = true;
    controls.autoRotateSpeed = 0.5;
    controlsRef.current = controls;

    // Add ambient light
    const ambientLight = new THREE.AmbientLight(0xffffff, 0.6);
    scene.add(ambientLight);

    // Add directional light
    const directionalLight = new THREE.DirectionalLight(0xffffff, 0.8);
    directionalLight.position.set(5, 5, 5);
    scene.add(directionalLight);

    // Create vertices
    const vertexGeometry = new THREE.SphereGeometry(0.15, 32, 32);
    vertexMeshesRef.current = [];

    vertices.forEach((v, idx) => {
      const color = colorFunction ? colorFunction(v.bits) : COLORS.cubeVertex;
      const material = new THREE.MeshPhongMaterial({ color });
      const mesh = new THREE.Mesh(vertexGeometry, material);
      mesh.position.copy(getPosition3D(v.bits));
      mesh.userData = { index: idx, bits: v.bits };
      scene.add(mesh);
      vertexMeshesRef.current.push(mesh);
    });

    // Create edges
    edgeLinesRef.current = [];
    const edgeMaterial = new THREE.LineBasicMaterial({
      color: COLORS.cubeEdge,
      opacity: 0.4,
      transparent: true
    });

    for (let i = 0; i < vertices.length; i++) {
      for (let j = i + 1; j < vertices.length; j++) {
        if (hammingDistance(vertices[i].bits, vertices[j].bits) === 1) {
          const points = [
            getPosition3D(vertices[i].bits),
            getPosition3D(vertices[j].bits),
          ];
          const geometry = new THREE.BufferGeometry().setFromPoints(points);
          const line = new THREE.Line(geometry, edgeMaterial.clone());
          line.userData = { from: i, to: j };
          scene.add(line);
          edgeLinesRef.current.push(line);
        }
      }
    }

    // Animation loop
    const animate = () => {
      animationRef.current = requestAnimationFrame(animate);
      controls.update();
      renderer.render(scene, camera);
    };
    animate();

    // Handle click
    const raycaster = new THREE.Raycaster();
    const mouse = new THREE.Vector2();

    const handleClick = (event: MouseEvent) => {
      const rect = renderer.domElement.getBoundingClientRect();
      mouse.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
      mouse.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;

      raycaster.setFromCamera(mouse, camera);
      const intersects = raycaster.intersectObjects(vertexMeshesRef.current);

      if (intersects.length > 0 && onVertexSelect) {
        const idx = intersects[0].object.userData.index;
        onVertexSelect(selectedVertex === idx ? null : idx);
      }
    };

    renderer.domElement.addEventListener('click', handleClick);

    return () => {
      cancelAnimationFrame(animationRef.current);
      renderer.domElement.removeEventListener('click', handleClick);
      if (containerRef.current && renderer.domElement) {
        containerRef.current.removeChild(renderer.domElement);
      }
      renderer.dispose();
    };
  }, [n, vertices, getPosition3D, colorFunction]);

  // Update vertex colors and highlights
  useEffect(() => {
    if (!sceneRef.current) return;

    vertexMeshesRef.current.forEach((mesh, idx) => {
      const isSelected = selectedVertex === idx;
      const isNeighbor = highlightNeighbors && selectedVertex !== null &&
        hammingDistance(vertices[selectedVertex].bits, vertices[idx].bits) === 1;

      let color: string;
      if (isSelected) {
        color = COLORS.cubeActive;
      } else if (isNeighbor) {
        color = COLORS.cubePositive;
      } else if (colorFunction) {
        color = colorFunction(vertices[idx].bits);
      } else {
        color = COLORS.cubeVertex;
      }

      (mesh.material as THREE.MeshPhongMaterial).color.set(color);
      mesh.scale.setScalar(isSelected ? 1.5 : isNeighbor ? 1.3 : 1);
    });

    // Update edge colors
    edgeLinesRef.current.forEach((line) => {
      const { from, to } = line.userData;
      const highlight = highlightNeighbors &&
        (selectedVertex === from || selectedVertex === to);

      const material = line.material as THREE.LineBasicMaterial;
      material.color.set(highlight ? COLORS.cubeActive : COLORS.cubeEdge);
      material.opacity = highlight ? 1 : 0.4;
    });
  }, [selectedVertex, highlightNeighbors, vertices, colorFunction]);

  return (
    <div
      ref={containerRef}
      className="w-[300px] h-[300px] mx-auto rounded-lg overflow-hidden shadow-lg"
      style={{ cursor: 'grab' }}
    />
  );
}

// ============================================================================
// NAVIGATION
// ============================================================================

function Navigation({
  currentSection,
  setSection
}: {
  currentSection: Section;
  setSection: (s: Section) => void;
}) {
  const sections: { id: Section; label: string; icon: string }[] = [
    { id: "intro", label: "The Conjecture", icon: "I" },
    { id: "cube", label: "The Hypercube", icon: "II" },
    { id: "sensitivity", label: "Sensitivity", icon: "III" },
    { id: "fourier", label: "Fourier Analysis", icon: "IV" },
    { id: "gTransform", label: "The g-Transform", icon: "V" },
    { id: "huang", label: "Huang's Matrix", icon: "VI" },
    { id: "spectral", label: "Spectral Bounds", icon: "VII" },
    { id: "proof", label: "The Proof", icon: "VIII" },
    { id: "leanProof", label: "Full Lean Code", icon: "IX" },
  ];

  return (
    <nav className="fixed top-0 left-0 right-0 z-50 bg-primer-paper border-b-2 border-primer-gold shadow-sm">
      <div className="max-w-6xl mx-auto px-4">
        <div className="flex items-center justify-between h-16">
          <h1 className="primer-heading text-lg text-primer-ink">
            The Sensitivity Conjecture
          </h1>
          <div className="flex gap-1">
            {sections.map((s) => (
              <button
                key={s.id}
                onClick={() => setSection(s.id)}
                className={`px-3 py-2 text-sm primer-text transition-all rounded ${
                  currentSection === s.id
                    ? "bg-primer-gold text-white"
                    : "text-primer-ink hover:bg-primer-gold-light"
                }`}
              >
                <span className="font-bold mr-1">{s.icon}.</span>
                <span className="hidden md:inline">{s.label}</span>
              </button>
            ))}
          </div>
        </div>
      </div>
    </nav>
  );
}

// ============================================================================
// SECTION WRAPPER
// ============================================================================

function SectionWrapper({
  title,
  subtitle,
  children
}: {
  title: string;
  subtitle?: string;
  children: React.ReactNode;
}) {
  return (
    <section className="min-h-screen pt-24 pb-16 px-4">
      <div className="max-w-4xl mx-auto">
        <div className="text-center mb-12">
          <h2 className="primer-heading text-4xl text-primer-ink mb-4">
            {title}
          </h2>
          {subtitle && (
            <p className="primer-text text-lg text-primer-accent">
              {subtitle}
            </p>
          )}
        </div>
        <div className="primer-text text-lg leading-relaxed">
          {children}
        </div>
      </div>
    </section>
  );
}

// ============================================================================
// INTERACTIVE COMPONENTS
// ============================================================================

function SensitivityDemo3D() {
  const [selectedVertex, setSelectedVertex] = useState<number | null>(0);
  const vertices = useMemo(() => generateVertices(3), []);

  const f = (bits: boolean[]): boolean => {
    const sum = bits.filter(b => b).length;
    return sum >= 2;
  };

  const colorFunc = (bits: boolean[]) => {
    return f(bits) ? COLORS.cubePositive : COLORS.cubeNegative;
  };

  const neighbors = selectedVertex !== null
    ? vertices.filter((v, i) =>
        i !== selectedVertex && hammingDistance(vertices[selectedVertex].bits, v.bits) === 1
      )
    : [];

  const flippingNeighbors = selectedVertex !== null
    ? neighbors.filter(v => f(v.bits) !== f(vertices[selectedVertex].bits))
    : [];

  return (
    <div className="flex flex-col items-center gap-6">
      <div className="text-center primer-text">
        <p className="mb-2">
          Function: <span className="primer-code">f(x) = majority(x)</span>
          <br />
          <span className="text-sm text-stone-500">(outputs 1 if at least 2 bits are 1)</span>
        </p>
        <p className="text-sm text-stone-500">
          <span className="inline-block w-3 h-3 rounded-full bg-cube-positive mr-1"></span> f=1 (green)
          <span className="inline-block w-3 h-3 rounded-full bg-cube-negative ml-3 mr-1"></span> f=0 (red)
        </p>
      </div>

      <ThreeHypercube
        n={3}
        colorFunction={colorFunc}
        onVertexSelect={setSelectedVertex}
        selectedVertex={selectedVertex}
        highlightNeighbors={false}
      />

      {selectedVertex !== null && (
        <div className="bg-primer-gold-light p-4 rounded-lg text-center">
          <p className="primer-text">
            At vertex <span className="primer-code">{vertices[selectedVertex].label}</span>
            (f={f(vertices[selectedVertex].bits) ? "1" : "0"}):
          </p>
          <p className="text-2xl font-bold text-primer-accent mt-2">
            Local sensitivity = {flippingNeighbors.length}
          </p>
          <p className="text-sm text-stone-600 mt-1">
            ({flippingNeighbors.length} neighbor{flippingNeighbors.length !== 1 ? "s" : ""} flip the output)
          </p>
        </div>
      )}
    </div>
  );
}

function ChiVisualizer() {
  const [selectedS, setSelectedS] = useState<number[]>([0, 1]);
  const vertices = useMemo(() => generateVertices(3), []);
  const n = 3;

  const toggleBit = (bit: number) => {
    if (selectedS.includes(bit)) {
      setSelectedS(selectedS.filter(b => b !== bit));
    } else {
      setSelectedS([...selectedS, bit].sort());
    }
  };

  return (
    <div className="flex flex-col items-center gap-6">
      <div className="flex gap-4 items-center">
        <span className="primer-text">Select S:</span>
        {Array.from({ length: n }, (_, i) => (
          <button
            key={i}
            onClick={() => toggleBit(i)}
            className={`w-10 h-10 rounded-full font-mono text-sm transition-all ${
              selectedS.includes(i)
                ? "bg-primer-gold text-white"
                : "bg-stone-200 text-stone-600 hover:bg-stone-300"
            }`}
          >
            x{i + 1}
          </button>
        ))}
      </div>

      <div className="primer-text text-center">
        S = {"{"}{selectedS.map(i => `x${i + 1}`).join(", ") || "empty"}{"}"}
      </div>

      <div className="grid grid-cols-4 gap-3">
        {vertices.map((v, idx) => {
          const chiVal = chi(selectedS, v.bits);
          return (
            <div
              key={idx}
              className={`p-3 rounded-lg text-center transition-all ${
                chiVal === 1
                  ? "bg-matrix-positive text-white"
                  : "bg-matrix-negative text-white"
              }`}
            >
              <div className="font-mono text-xs">{v.label}</div>
              <div className="text-lg font-bold">{chiVal === 1 ? "+1" : "-1"}</div>
            </div>
          );
        })}
      </div>

      <div className="text-center primer-text text-sm text-stone-600 max-w-md">
        The parity character measures whether an even or odd number of bits in S are set to 1.
        Notice how adjacent vertices always have opposite signs when S contains all coordinates!
      </div>
    </div>
  );
}

function HuangMatrixViz() {
  const [n, setN] = useState(2);

  const buildHuangMatrix = useCallback((size: number): number[][] => {
    if (size === 1) {
      return [[0, 1], [1, 0]];
    }
    const An = buildHuangMatrix(size - 1);
    const dim = An.length;
    const result: number[][] = Array(dim * 2).fill(null).map(() => Array(dim * 2).fill(0));

    for (let i = 0; i < dim; i++) {
      for (let j = 0; j < dim; j++) {
        result[i][j] = An[i][j];
      }
    }
    for (let i = 0; i < dim; i++) {
      result[i][dim + i] = 1;
    }
    for (let i = 0; i < dim; i++) {
      result[dim + i][i] = 1;
    }
    for (let i = 0; i < dim; i++) {
      for (let j = 0; j < dim; j++) {
        result[dim + i][dim + j] = -An[i][j];
      }
    }
    return result;
  }, []);

  const matrix = useMemo(() => buildHuangMatrix(n), [n, buildHuangMatrix]);
  const sqrtN = Math.sqrt(n).toFixed(2);

  return (
    <div className="flex flex-col items-center gap-6">
      <div className="flex gap-4 items-center">
        <span className="primer-text">Dimension n:</span>
        {[1, 2, 3].map(dim => (
          <button
            key={dim}
            onClick={() => setN(dim)}
            className={`w-10 h-10 rounded-full font-mono transition-all ${
              n === dim
                ? "bg-primer-gold text-white"
                : "bg-stone-200 text-stone-600 hover:bg-stone-300"
            }`}
          >
            {dim}
          </button>
        ))}
      </div>

      <div className="overflow-x-auto">
        <div
          className="grid gap-1 p-4 bg-stone-100 rounded-lg"
          style={{ gridTemplateColumns: `repeat(${matrix.length}, minmax(2rem, 1fr))` }}
        >
          {matrix.flatMap((row, i) =>
            row.map((val, j) => (
              <div
                key={`${i}-${j}`}
                className={`w-8 h-8 flex items-center justify-center text-sm font-mono rounded ${
                  val > 0
                    ? "bg-matrix-positive text-white"
                    : val < 0
                    ? "bg-matrix-negative text-white"
                    : "bg-matrix-zero text-stone-400"
                }`}
              >
                {val > 0 ? "+" : val < 0 ? "-" : "0"}
              </div>
            ))
          )}
        </div>
      </div>

      <div className="bg-primer-gold-light p-4 rounded-lg text-center max-w-md">
        <p className="primer-text font-semibold mb-2">Key Properties:</p>
        <ul className="text-left primer-text text-sm space-y-1">
          <li>Matrix size: {matrix.length} x {matrix.length}</li>
          <li>Eigenvalues: exactly <Latex>{`\\pm\\sqrt{${n}} = \\pm${sqrtN}`}</Latex></li>
          <li>Each eigenvalue has multiplicity {matrix.length / 2}</li>
          <li>The nonzero pattern matches the hypercube adjacency!</li>
        </ul>
      </div>
    </div>
  );
}

function LevelSetViz() {
  const vertices = useMemo(() => generateVertices(3), []);

  const f = (bits: boolean[]): number => bits.filter(b => b).length >= 2 ? 1 : 0;

  const chiUniv = (bits: boolean[]): number => {
    const sum = bits.filter(b => b).length;
    return sum % 2 === 0 ? 1 : -1;
  };

  const g = (bits: boolean[]): number => {
    return (f(bits) === 1 ? -1 : 1) * chiUniv(bits);
  };

  const sPos = vertices.filter(v => g(v.bits) === 1);
  const sNeg = vertices.filter(v => g(v.bits) === -1);
  const larger = sPos.length > sNeg.length ? "S+" : "S-";

  const colorFunc = (bits: boolean[]) => {
    return g(bits) === 1 ? COLORS.cubePositive : COLORS.cubeNegative;
  };

  return (
    <div className="flex flex-col items-center gap-6">
      <ThreeHypercube n={3} colorFunction={colorFunc} />

      <div className="flex gap-8">
        <div className="text-center">
          <h4 className="primer-heading text-lg mb-3">S+ (g = +1)</h4>
          <div className="flex flex-wrap gap-2 justify-center max-w-32">
            {sPos.map((v, i) => (
              <div key={i} className="bg-cube-positive text-white px-2 py-1 rounded font-mono text-sm">
                {v.label}
              </div>
            ))}
          </div>
          <p className="mt-2 font-bold">|S+| = {sPos.length}</p>
        </div>

        <div className="text-center">
          <h4 className="primer-heading text-lg mb-3">S- (g = -1)</h4>
          <div className="flex flex-wrap gap-2 justify-center max-w-32">
            {sNeg.map((v, i) => (
              <div key={i} className="bg-cube-negative text-white px-2 py-1 rounded font-mono text-sm">
                {v.label}
              </div>
            ))}
          </div>
          <p className="mt-2 font-bold">|S-| = {sNeg.length}</p>
        </div>
      </div>

      <div className="bg-primer-gold-light p-4 rounded-lg text-center max-w-lg">
        <p className="primer-text">
          Since {sPos.length} + {sNeg.length} = {vertices.length} = 2^3, and they're unequal...
        </p>
        <p className="text-xl font-bold text-primer-accent mt-2">
          |{larger}| = {Math.max(sPos.length, sNeg.length)} {">"} 2^{3 - 1} = 4
        </p>
        <p className="text-sm text-stone-600 mt-2">
          This large level set is where the spectral bound applies!
        </p>
      </div>
    </div>
  );
}

function SpectralBoundViz() {
  const steps = [
    { label: "\\sqrt{n}", desc: "Lower bound on eigenvalue", color: COLORS.cubePositive },
    { label: "\\lambda_{\\max}(A[S])", desc: "Largest eigenvalue of submatrix", color: COLORS.primerGold },
    { label: "\\text{maxDeg}(G[S])", desc: "Max degree in induced graph", color: COLORS.cubeVertex },
    { label: "s(f)", desc: "Sensitivity of f", color: COLORS.primerAccent },
  ];

  return (
    <div className="flex flex-col items-center gap-6">
      <div className="flex items-center gap-2 flex-wrap justify-center">
        {steps.map((step, i) => (
          <React.Fragment key={i}>
            <div
              className="p-4 rounded-lg text-center text-white min-w-28"
              style={{ backgroundColor: step.color }}
            >
              <div className="font-bold text-lg"><Latex>{step.label}</Latex></div>
              <div className="text-xs mt-1 opacity-90">{step.desc}</div>
            </div>
            {i < steps.length - 1 && (
              <div className="text-2xl font-bold text-stone-400"><Latex>{"\\leq"}</Latex></div>
            )}
          </React.Fragment>
        ))}
      </div>

      <div className="bg-stone-100 p-6 rounded-lg max-w-2xl">
        <p className="primer-text text-center">
          This chain of inequalities is the heart of the proof:
        </p>
        <ol className="list-decimal list-inside mt-4 space-y-2 primer-text">
          <li><strong>Interlacing:</strong> A large submatrix inherits a large eigenvalue</li>
          <li><strong>Row-sum bound:</strong> Eigenvalues are bounded by graph degrees</li>
          <li><strong>Level set property:</strong> Induced degrees equal sensitivity counts</li>
        </ol>
      </div>
    </div>
  );
}

function ProofFlowViz() {
  const nodes = [
    { id: "degree", label: "degree(f) = n", x: 200, y: 50, color: COLORS.cubeVertex },
    { id: "fourier", label: "f̂([n]) ≠ 0", x: 200, y: 120, color: COLORS.cubeVertex },
    { id: "gtransform", label: "Σg ≠ 0", x: 200, y: 190, color: COLORS.cubeEdge },
    { id: "levelset", label: "|S| > 2^(n-1)", x: 200, y: 260, color: COLORS.cubeEdge },
    { id: "spectral", label: "λ ≥ √n", x: 100, y: 330, color: COLORS.cubePositive },
    { id: "graph", label: "maxDeg ≥ √n", x: 300, y: 330, color: COLORS.cubePositive },
    { id: "sensitivity", label: "s(f) ≥ √n", x: 200, y: 400, color: COLORS.cubeActive },
  ];

  const edges = [
    { from: "degree", to: "fourier" },
    { from: "fourier", to: "gtransform" },
    { from: "gtransform", to: "levelset" },
    { from: "levelset", to: "spectral" },
    { from: "levelset", to: "graph" },
    { from: "spectral", to: "sensitivity" },
    { from: "graph", to: "sensitivity" },
  ];

  const nodeMap = Object.fromEntries(nodes.map(n => [n.id, n]));

  return (
    <div className="flex justify-center">
      <svg viewBox="0 0 400 460" className="w-full max-w-md">
        {edges.map((e, i) => {
          const from = nodeMap[e.from];
          const to = nodeMap[e.to];
          return (
            <line
              key={i}
              x1={from.x}
              y1={from.y + 15}
              x2={to.x}
              y2={to.y - 15}
              stroke="#999"
              strokeWidth={2}
              markerEnd="url(#arrowhead)"
            />
          );
        })}
        <defs>
          <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
            <polygon points="0 0, 10 3.5, 0 7" fill="#999" />
          </marker>
        </defs>
        {nodes.map((node) => (
          <g key={node.id}>
            <rect
              x={node.x - 70}
              y={node.y - 15}
              width={140}
              height={30}
              rx={6}
              fill={node.color}
            />
            <text
              x={node.x}
              y={node.y + 4}
              textAnchor="middle"
              fill="white"
              fontSize="12"
              fontFamily="Georgia, serif"
              fontWeight="bold"
            >
              {node.label}
            </text>
          </g>
        ))}
      </svg>
    </div>
  );
}

// ============================================================================
// SECTION CONTENT
// ============================================================================

function IntroSection() {
  return (
    <SectionWrapper
      title="The Sensitivity Conjecture"
      subtitle="An Illustrated Primer"
    >
      <div className="space-y-8">
        <div className="primer-border p-8 bg-white rounded-lg">
          <p className="text-center text-xl italic">
            "For any Boolean function f on n bits,"
          </p>
          <div className="text-center my-4">
            <Latex display>{"s(f) \\geq \\sqrt{\\deg(f)}"}</Latex>
          </div>
          <p className="text-center text-sm text-stone-500">
            — Hao Huang, 2019
          </p>
        </div>

        <p>
          Imagine a machine with <em>n</em> on/off switches. Each combination of switch
          positions produces an output: either ON or OFF. This is a <strong>Boolean function</strong>.
        </p>

        <p>
          Two questions arise naturally:
        </p>

        <div className="grid md:grid-cols-2 gap-6 my-8">
          <div className="bg-cube-positive/10 p-6 rounded-lg border-l-4 border-cube-positive">
            <h3 className="primer-heading text-lg mb-2">Sensitivity</h3>
            <p className="text-sm">
              At the most "fragile" switch setting, how many single switches can
              change the output when flipped?
            </p>
          </div>
          <div className="bg-cube-vertex/10 p-6 rounded-lg border-l-4 border-cube-vertex">
            <h3 className="primer-heading text-lg mb-2">Degree</h3>
            <p className="text-sm">
              What is the largest group of switches that ever "interact together"
              in determining the output?
            </p>
          </div>
        </div>

        <p>
          For decades, mathematicians suspected these measures were tightly linked.
          In 2019, Hao Huang proved it with an elegant spectral argument.
          This primer will guide you through the proof, step by step, following the
          Lean formalization.
        </p>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">The Final Theorem in Lean</h4>
          <LeanCode title="sensitivity.lean">
{`theorem sensitivity_conjecture {n : Nat} (f : (Fin n -> Bool) -> Bool) :
  (sensitivity f : Real) >= Real.sqrt (degree f) := by
  -- pick S with f_hat(S) != 0
  -- restrict to get full degree on S
  -- apply full-degree theorem
  -- use sensitivity monotonicity
  ...`}
          </LeanCode>
          <p className="text-sm mt-4">
            We'll explore each piece of this proof, understanding what the Lean code formalizes
            and why each step works.
          </p>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">What You'll Learn</h4>
          <ul className="space-y-2">
            <li>The hypercube as a graph — where inputs live</li>
            <li>Sensitivity — measuring local instability</li>
            <li>Fourier analysis — decomposing functions into parity patterns</li>
            <li>The g-transform — creating an imbalanced coloring</li>
            <li>Huang's matrix — a spectral gadget with clean eigenvalues</li>
            <li>Interlacing — connecting eigenvalues to graph degrees</li>
            <li>The final assembly — putting it all together</li>
          </ul>
        </div>
      </div>
    </SectionWrapper>
  );
}

function CubeSection() {
  const [selectedVertex, setSelectedVertex] = useState<number | null>(null);
  const vertices = useMemo(() => generateVertices(3), []);

  return (
    <SectionWrapper
      title="The Boolean Hypercube"
      subtitle="Where inputs live"
    >
      <div className="space-y-8">
        <p>
          An <em>n</em>-bit string is just a sequence of 0s and 1s, like{" "}
          <span className="primer-code">010</span> or{" "}
          <span className="primer-code">111</span>. The set of all such strings
          forms the vertices of an <strong>n-dimensional hypercube</strong>.
        </p>

        <div className="grid md:grid-cols-2 gap-8 my-8">
          <div className="text-center">
            <h4 className="primer-heading mb-4">2D Hypercube (n=2)</h4>
            <ThreeHypercube n={2} />
            <p className="text-sm text-stone-500 mt-2">4 vertices, 4 edges</p>
          </div>
          <div className="text-center">
            <h4 className="primer-heading mb-4">3D Hypercube (n=3)</h4>
            <ThreeHypercube
              n={3}
              highlightNeighbors
              selectedVertex={selectedVertex}
              onVertexSelect={setSelectedVertex}
            />
            <p className="text-sm text-stone-500 mt-2">
              8 vertices, 12 edges
              {selectedVertex !== null && (
                <span className="block mt-1">
                  <span className="primer-code">{vertices[selectedVertex].label}</span> has 3 neighbors
                </span>
              )}
            </p>
          </div>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border">
          <h4 className="primer-heading text-lg mb-3">Neighbors</h4>
          <p>
            Two vertices are <strong>neighbors</strong> if they differ in exactly one bit.
            In the graph above, this means they're connected by an edge.
          </p>
          <p className="mt-3">
            For example, <span className="primer-code">000</span> and{" "}
            <span className="primer-code">001</span> are neighbors (differ only in the last bit),
            but <span className="primer-code">000</span> and{" "}
            <span className="primer-code">011</span> are not (differ in two bits).
          </p>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg">
          <h4 className="primer-heading text-lg mb-3">In Lean: The Boolean Cube</h4>
          <p className="mb-4">
            The Lean formalization represents n-bit strings as functions from <code>Fin n</code>
            to <code>Bool</code>. Two inputs are neighbors when they differ in exactly one coordinate:
          </p>
          <LeanCode title="BC1: Neighbor definition">
{`-- Two inputs are neighbors if they differ in exactly one bit
def are_neighbors {n : Nat} (x y : Fin n -> Bool) : Prop :=
  (Finset.filter (fun i => x i != y i) Finset.univ).card = 1`}
          </LeanCode>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border">
          <h4 className="primer-heading text-lg mb-3">Key Insight</h4>
          <p>
            Every vertex in the n-dimensional hypercube has exactly <strong>n neighbors</strong>.
            This is because you can flip any one of the n bits to get a neighbor.
          </p>
        </div>
      </div>
    </SectionWrapper>
  );
}

function SensitivitySection() {
  return (
    <SectionWrapper
      title="Sensitivity"
      subtitle="Measuring fragility"
    >
      <div className="space-y-8">
        <p>
          Given a Boolean function f, the <strong>sensitivity at input x</strong> counts
          how many single-bit changes flip the output. In formal notation:
        </p>

        <div className="bg-white p-6 rounded-lg primer-border text-center">
          <Latex display>{"\\text{local\\_sensitivity}(f, x) = |\\{ y : x \\sim y \\text{ and } f(x) \\neq f(y) \\}|"}</Latex>
        </div>

        <p>
          The <strong>global sensitivity</strong> <Latex>{"s(f)"}</Latex> is the maximum over all inputs:
        </p>

        <div className="bg-primer-accent text-white p-6 rounded-lg text-center">
          <Latex display>{"s(f) = \\max_x \\text{local\\_sensitivity}(f, x)"}</Latex>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: Sensitivity Definition (SEN0)</h4>
          <p className="mb-4">
            The Lean formalization defines sensitivity by filtering all inputs y that differ from x
            in exactly one coordinate, and also flip the output:
          </p>
          <LeanCode title="sensitivity.lean">
{`def sensitivity {n : Nat} (f : (Fin n -> Bool) -> Bool) : Nat :=
  Finset.sup Finset.univ (fun x =>
    Finset.card (Finset.filter (fun y =>
      (Finset.card (Finset.filter (fun i => x i != y i) Finset.univ) = 1)
      && (f x != f y)
    ) Finset.univ))`}
          </LeanCode>
          <p className="text-sm mt-4">
            Read it as: for each x, count all y at Hamming distance 1 with f(x) ≠ f(y),
            then take the maximum.
          </p>
        </div>

        <h3 className="primer-heading text-2xl mt-12 mb-6">Interactive Demo</h3>

        <SensitivityDemo3D />

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">Graph Perspective</h4>
          <p>
            Think of the Boolean function as coloring each vertex of the hypercube
            green (output 1) or red (output 0). Sensitivity counts how many edges
            cross from green to red at the "worst" vertex.
          </p>
        </div>

        <div className="bg-stone-100 p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">Quick Examples</h4>
          <ul className="space-y-3">
            <li>
              <strong>Parity function:</strong> f(x) = XOR of all n bits. Flipping any one bit changes parity,
              so every input has local sensitivity n. Therefore <Latex>{"s(f) = n"}</Latex>.
            </li>
            <li>
              <strong>First bit function:</strong> f(x) = x₁. Only flipping the first bit changes the value,
              so local sensitivity is always 1, and <Latex>{"s(f) = 1"}</Latex>.
            </li>
          </ul>
        </div>
      </div>
    </SectionWrapper>
  );
}

function FourierSection() {
  return (
    <SectionWrapper
      title="Fourier Analysis"
      subtitle="Decomposing into parity patterns"
    >
      <div className="space-y-8">
        <p>
          Just as sound can be decomposed into pure frequencies, Boolean functions
          can be decomposed into <strong>parity characters</strong>. These are the
          basic "waves" in the Fourier analysis of Boolean functions.
        </p>

        <div className="bg-white p-6 rounded-lg primer-border">
          <h4 className="primer-heading text-lg mb-3">The Parity Character <Latex>{"\\chi_S"}</Latex> (CHI0)</h4>
          <p>
            For a subset S of coordinates, the character <Latex>{"\\chi_S"}</Latex> outputs +1 if an{" "}
            <strong>even</strong> number of bits in S are 1, and -1 if <strong>odd</strong>:
          </p>
          <Latex display>{"\\chi_S(x) = (-1)^{|S \\cap x|}"}</Latex>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg">
          <h4 className="primer-heading text-lg mb-3">In Lean: Parity Character</h4>
          <LeanCode title="sensitivity.lean (CHI0)">
{`def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1`}
          </LeanCode>
          <p className="text-sm mt-4">
            Read this as: filter S to the indices where x is true, count them,
            and check whether the count is even. Even → 1, odd → -1.
          </p>
        </div>

        <h3 className="primer-heading text-2xl mt-12 mb-6">Interactive: Explore <Latex>{"\\chi_S"}</Latex></h3>

        <ChiVisualizer />

        <div className="mt-12 space-y-6">
          <h4 className="primer-heading text-xl">Fourier Coefficients & Degree</h4>

          <p>
            Every Boolean function can be written as a weighted sum of parity characters:
          </p>

          <div className="bg-stone-100 p-4 rounded-lg text-center">
            <Latex display>{"f(x) = \\sum_S \\hat{f}(S) \\cdot \\chi_S(x)"}</Latex>
          </div>

          <p>
            The <strong>Fourier coefficient</strong> <Latex>{"\\hat{f}(S)"}</Latex> measures how much f correlates
            with the parity pattern <Latex>{"\\chi_S"}</Latex>:
          </p>

          <div className="bg-white p-6 rounded-lg primer-border">
            <Latex display>{"\\hat{f}(S) = \\frac{1}{2^n} \\sum_{x \\in \\{0,1\\}^n} f(x) \\cdot \\chi_S(x)"}</Latex>
          </div>

          <div className="bg-primer-gold-light p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">In Lean: Fourier Coefficient (FOURIER0)</h4>
            <LeanCode title="sensitivity.lean">
{`noncomputable def fourier_coeff {n : Nat}
    (f : (Fin n -> Bool) -> Bool) (S : Finset (Fin n)) : Real :=
  (Finset.sum Finset.univ (fun x =>
    (if f x then 1 else 0) * chi S x)) / 2^n`}
            </LeanCode>
          </div>

          <div className="bg-primer-accent text-white p-6 rounded-lg">
            <h5 className="font-bold mb-2">Degree of f (DEG0)</h5>
            <p>
              The <strong>degree</strong> of f is the largest |S| such that <Latex>{"\\hat{f}(S) \\neq 0"}</Latex>.
              It measures the largest group of bits that "interact together" in f.
            </p>
            <LeanCode title="sensitivity.lean">
{`noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card`}
            </LeanCode>
          </div>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">Key Fact for the Proof (FULLCOEF)</h4>
          <p>
            If degree(f) = n, then <Latex>{"\\hat{f}([n]) \\neq 0"}</Latex> — the coefficient on the "full parity"
            pattern is nonzero. This will be crucial in the next step.
          </p>
        </div>
      </div>
    </SectionWrapper>
  );
}

function GTransformSection() {
  return (
    <SectionWrapper
      title="The g-Transform"
      subtitle="Creating imbalance"
    >
      <div className="space-y-8">
        <p>
          Now comes a clever trick. We define a new function g by twisting f with
          the full parity character:
        </p>

        <div className="bg-white p-6 rounded-lg primer-border text-center">
          <Latex display>{"g(x) = \\begin{cases} -1 & \\text{if } f(x) = 1 \\\\ +1 & \\text{if } f(x) = 0 \\end{cases} \\cdot \\chi_{[n]}(x)"}</Latex>
        </div>

        <p>
          The function g only takes values +1 and -1. Here's the magic:
        </p>

        <div className="bg-primer-accent text-white p-6 rounded-lg">
          <p className="font-bold text-lg mb-2">
            If degree(f) = n, then the sum of g over all vertices is nonzero.
          </p>
          <p className="text-sm opacity-90">
            This follows from <Latex>{"\\hat{f}([n]) \\neq 0"}</Latex> and the orthogonality of Fourier characters.
          </p>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: The g-Transform (GVAL0)</h4>
          <LeanCode title="sensitivity.lean">
{`def g_val {n : Nat} (f : (Fin n -> Bool) -> Bool) (x : Fin n -> Bool) : Real :=
  (if f x then -1 else 1) * chi Finset.univ x

lemma g_val_sum_ne_zero {n : Nat} (f : (Fin n -> Bool) -> Bool)
  (h_deg : degree f = n) (hn : n != 0) :
  Finset.sum Finset.univ (g_val f) != 0 := by
  ...`}
          </LeanCode>
          <p className="text-sm mt-4">
            The key insight: since g(x) = ±1 always, and the sum is nonzero, one sign
            must appear more often than the other!
          </p>
        </div>

        <h3 className="primer-heading text-2xl mt-12 mb-6">Level Sets (LEVELSETS)</h3>

        <p>
          Since g takes only values +1 and -1, we can partition all vertices into two sets:
        </p>

        <div className="bg-white p-6 rounded-lg primer-border mb-6">
          <div className="grid md:grid-cols-2 gap-4">
            <div>
              <Latex display>{"S^+ = \\{ x : g(x) = +1 \\}"}</Latex>
            </div>
            <div>
              <Latex display>{"S^- = \\{ x : g(x) = -1 \\}"}</Latex>
            </div>
          </div>
        </div>

        <LevelSetViz />

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: Level Sets</h4>
          <LeanCode title="sensitivity.lean (LEVELSETS)">
{`def S_pos {n : Nat} (f : (Fin n -> Bool) -> Bool) : Finset (Fin n -> Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : Nat} (f : (Fin n -> Bool) -> Bool) : Finset (Fin n -> Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ

lemma exists_large_level_set {n : Nat} (f : (Fin n -> Bool) -> Bool)
  (h_deg : degree f = n) (hn : n != 0) :
  (S_pos f).card > 2^(n-1) or (S_neg f).card > 2^(n-1) := by
  -- Use sum g_val != 0 to show |S_pos| != |S_neg|,
  -- then use |S_pos| + |S_neg| = 2^n.
  ...`}
          </LeanCode>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">The Parity Flip Property (NEIGH_PARITY)</h4>
          <p>
            Along any edge of the hypercube (neighbors differing in one bit), the parity
            <Latex>{"\\chi_{[n]}"}</Latex> flips sign. This leads to a remarkable equivalence:
          </p>
          <div className="bg-stone-100 p-4 rounded mt-4">
            <Latex display>{"\\text{For neighbors } x \\sim y: \\quad g(x) = g(y) \\iff f(x) \\neq f(y)"}</Latex>
          </div>
          <p className="mt-4 text-sm">
            In words: within a level set, neighbors in the <em>graph</em> are exactly
            the neighbors where <em>f flips</em>. So the induced degree equals the sensitivity count!
          </p>
        </div>
      </div>
    </SectionWrapper>
  );
}

function HuangSection() {
  return (
    <SectionWrapper
      title="Huang's Matrix"
      subtitle="The spectral gadget"
    >
      <div className="space-y-8">
        <p>
          Hao Huang's key insight was to construct a special matrix <Latex>{"A_n"}</Latex> related to the
          hypercube. Its eigenvalues are perfectly balanced: exactly <Latex>{"+\\sqrt{n}"}</Latex> and <Latex>{"-\\sqrt{n}"}</Latex>.
        </p>

        <div className="bg-white p-6 rounded-lg primer-border">
          <h4 className="primer-heading text-lg mb-3">Recursive Definition (HUANG_DEF)</h4>
          <p className="mb-4">
            <Latex>{"A_1"}</Latex> is the 2×2 matrix with 0s on the diagonal and 1s off-diagonal.
            For n+1, we build <Latex>{"A_{n+1}"}</Latex> in blocks:
          </p>
          <Latex display>{"A_{n+1} = \\begin{pmatrix} A_n & I_{2^n} \\\\ I_{2^n} & -A_n \\end{pmatrix}"}</Latex>
          <p className="text-sm text-stone-600 mt-4">
            The minus sign in the bottom-right is the magic ingredient that makes the spectrum clean!
          </p>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg">
          <h4 className="primer-heading text-lg mb-3">In Lean: Huang Matrix</h4>
          <LeanCode title="sensitivity.lean (HUANG_DEF)">
{`def huang_matrix (n : Nat) : Matrix (Fin n -> Bool) (Fin n -> Bool) Real :=
  match n with
  | 0 => 0
  | n + 1 =>
      Matrix.reindex (finSuccEquiv_huang_custom n).symm
                     (finSuccEquiv_huang_custom n).symm
        (Matrix.fromBlocks (huang_matrix n) 1 1 (-huang_matrix n))`}
          </LeanCode>
          <p className="text-sm mt-4">
            The <code>reindex</code> handles bookkeeping so the block matrix is indexed by
            actual (n+1)-bit strings.
          </p>
        </div>

        <h3 className="primer-heading text-2xl mt-12 mb-6">Explore the Matrix</h3>

        <HuangMatrixViz />

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">The Spectrum (HUANG_SPEC)</h4>
          <p className="mb-4">
            The eigenvalues of <Latex>{"A_n"}</Latex> are exactly <Latex>{"\\pm\\sqrt{n}"}</Latex>, each with
            multiplicity <Latex>{"2^{n-1}"}</Latex>. Why?
          </p>
          <ol className="list-decimal list-inside space-y-2">
            <li><Latex>{"A_n^2 = nI"}</Latex>, so eigenvalues satisfy <Latex>{"\\lambda^2 = n"}</Latex></li>
            <li><Latex>{"\\text{trace}(A_n) = 0"}</Latex>, so the sum of eigenvalues is zero</li>
            <li>Matrix size is <Latex>{"2^n"}</Latex>, so half are positive, half negative</li>
          </ol>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: Spectrum Theorem</h4>
          <LeanCode title="sensitivity.lean (HUANG_SPEC)">
{`theorem huang_eigenvalues_eq_list (n : Nat) (hn : n != 0) :
  let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
  evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++
        List.replicate (2^(n-1)) (Real.sqrt n) := by
  ...`}
          </LeanCode>
        </div>

        <div className="bg-stone-100 p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">Why This Matrix Matters</h4>
          <ul className="space-y-2">
            <li>
              <strong>Clean spectrum:</strong> Eigenvalues are exactly <Latex>{"\\pm\\sqrt{n}"}</Latex>, making
              spectral bounds easy to compute.
            </li>
            <li>
              <strong>Matches hypercube:</strong> The nonzero pattern (ignoring signs)
              is exactly the adjacency matrix of the hypercube graph.
            </li>
            <li>
              <strong>Interlacing applies:</strong> Large principal submatrices inherit
              large eigenvalues.
            </li>
          </ul>
        </div>
      </div>
    </SectionWrapper>
  );
}

function SpectralSection() {
  return (
    <SectionWrapper
      title="Spectral Bounds"
      subtitle="Connecting eigenvalues to degrees"
    >
      <div className="space-y-8">
        <p>
          The final steps use two spectral principles to create a chain of inequalities.
        </p>

        <div className="grid md:grid-cols-2 gap-6 my-8">
          <div className="bg-cube-positive/10 p-6 rounded-lg border-l-4 border-cube-positive">
            <h4 className="primer-heading text-lg mb-2">Interlacing (INTERLACE)</h4>
            <p className="text-sm">
              If S has more than half the vertices, then the largest eigenvalue of
              the submatrix <Latex>{"A_n[S]"}</Latex> is at least <Latex>{"\\sqrt{n}"}</Latex>.
            </p>
            <Latex display>{"\\lambda_{\\max}(A_n[S]) \\geq \\sqrt{n}"}</Latex>
          </div>
          <div className="bg-cube-vertex/10 p-6 rounded-lg border-l-4 border-cube-vertex">
            <h4 className="primer-heading text-lg mb-2">Row-Sum Bound (SPEC_UPPER)</h4>
            <p className="text-sm">
              The largest eigenvalue is bounded by the maximum row sum, which
              corresponds to the maximum degree in the induced graph.
            </p>
            <Latex display>{"\\lambda_{\\max}(A_n[S]) \\leq \\text{maxDeg}(G[S])"}</Latex>
          </div>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg">
          <h4 className="primer-heading text-lg mb-3">In Lean: Interlacing Lower Bound (HUANG_SUB_LOWER)</h4>
          <LeanCode title="sensitivity.lean">
{`/- The largest eigenvalue of a principal submatrix of size m
   is at least the m-th smallest eigenvalue of the original matrix. -/
lemma eigenvalue_interlacing_max ... :
  lambda_max(A[S]) >= lambda_{m-1}(A)`}
          </LeanCode>
          <p className="text-sm mt-4">
            Combined with HUANG_SPEC: if |S| &gt; 2^(n-1), then <Latex>{"\\lambda_{\\max}(A_n[S]) \\geq \\sqrt{n}"}</Latex>.
          </p>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: Spectral Upper Bound (SPEC_UPPER)</h4>
          <LeanCode title="sensitivity.lean">
{`theorem spectral_radius_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (G : SimpleGraph (Fin n))
  (h_adj : ∀ i j, |A i j| ≤ if G.Adj i j then 1 else 0) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues A hA
  let lambda_max := evs.getLast ...
  lambda_max ≤ G.maxDegree := by ...`}
          </LeanCode>
        </div>

        <h3 className="primer-heading text-2xl mt-12 mb-6">The Chain of Inequalities</h3>

        <SpectralBoundViz />

        <div className="bg-primer-accent text-white p-6 rounded-lg mt-8">
          <h4 className="font-bold text-lg mb-3">Connecting to Sensitivity (DEG_SENS_LEVEL)</h4>
          <p>
            The induced graph degree equals the sensitivity count (from the g-transform
            parity flip property). So maxDeg(G[S]) ≤ sensitivity(f), completing the chain!
          </p>
          <LeanCode title="sensitivity.lean">
{`lemma induced_degree_le_sensitivity {n : Nat} (f : (Fin n -> Bool) -> Bool)
  (S : Finset (Fin n -> Bool)) (hS : is_level_set_of_g f S) :
  (induced_hypercube_graph S).maxDegree <= sensitivity f := by
  -- For vertex x in S, neighbors in S are exactly where f flips
  ...`}
          </LeanCode>
        </div>
      </div>
    </SectionWrapper>
  );
}

function ProofSection() {
  return (
    <SectionWrapper
      title="The Complete Proof"
      subtitle="Putting it all together"
    >
      <div className="space-y-8">
        <p>
          Let's trace the full proof for the case where degree(f) = n, following the Lean formalization.
        </p>

        <ProofFlowViz />

        <div className="space-y-6 mt-12">
          <div className="bg-stone-100 p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">Step 1: Full Degree → Nonzero Top Coefficient (FULLCOEF)</h4>
            <p>
              If degree(f) = n, then <Latex>{"\\hat{f}([n]) \\neq 0"}</Latex>. The function has a nonzero correlation
              with the full parity pattern.
            </p>
          </div>

          <div className="bg-stone-100 p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">Step 2: g-Transform Has Nonzero Sum (GVAL0)</h4>
            <p>
              Define <Latex>{"g(x) = (f(x) \\,?\\, {-1} : {+1}) \\cdot \\chi_{[n]}(x)"}</Latex>. By Fourier orthogonality,
              the sum of g over all vertices is nonzero.
            </p>
          </div>

          <div className="bg-stone-100 p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">Step 3: Large Level Set (LEVELSETS)</h4>
            <p>
              Since <Latex>{"g \\in \\{+1, -1\\}"}</Latex> and the sum is nonzero, one level set S has size <Latex>{"> 2^{n-1}"}</Latex>.
            </p>
          </div>

          <div className="bg-stone-100 p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">Step 4: Spectral Sandwich</h4>
            <p className="mb-2">
              Apply interlacing (HUANG_SUB_LOWER): <Latex>{"\\lambda_{\\max}(A_n[S]) \\geq \\sqrt{n}"}</Latex>
            </p>
            <p className="mb-2">
              Apply row-sum bound (SPEC_UPPER): <Latex>{"\\lambda_{\\max}(A_n[S]) \\leq \\text{maxDeg}(G[S])"}</Latex>
            </p>
            <p>
              Therefore: <Latex>{"\\text{maxDeg}(G[S]) \\geq \\sqrt{n}"}</Latex>
            </p>
          </div>

          <div className="bg-stone-100 p-6 rounded-lg">
            <h4 className="primer-heading text-lg mb-3">Step 5: Degree = Sensitivity (DEG_SENS_LEVEL)</h4>
            <p>
              By the parity flip property, the induced degree in S equals the
              sensitivity count. So: <Latex>{"s(f) \\geq \\text{maxDeg}(G[S]) \\geq \\sqrt{n}"}</Latex>
            </p>
          </div>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">In Lean: The Full-Degree Theorem (FULLCASE)</h4>
          <LeanCode title="sensitivity.lean">
{`theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : Nat}
  (f : (Fin n -> Bool) -> Bool) (h_deg : degree f = n) (hn : n != 0) :
  (sensitivity f : Real) >= Real.sqrt n := by
  -- 1. Get large level set S from LEVELSETS
  -- 2. Apply HUANG_SUB_LOWER: lambda_max >= sqrt(n)
  -- 3. Apply SPEC_UPPER: lambda_max <= maxDegree(G[S])
  -- 4. Apply DEG_SENS_LEVEL: maxDegree(G[S]) <= sensitivity(f)
  ...`}
          </LeanCode>
        </div>

        <div className="bg-primer-accent text-white p-8 rounded-lg mt-12 text-center">
          <h4 className="text-2xl font-bold mb-4">The General Case (REDUCE)</h4>
          <p className="text-lg mb-4">
            For arbitrary degree k = degree(f), we restrict f to a k-dimensional subcube
            where it has full degree, apply FULLCASE, and note that sensitivity
            can only decrease under restriction (SENS_MONO).
          </p>
          <LeanCode title="sensitivity.lean (REDUCE → GOAL)">
{`theorem sensitivity_conjecture {n : Nat} (f : (Fin n -> Bool) -> Bool) :
  (sensitivity f : Real) >= Real.sqrt (degree f) := by
  -- 1. Pick S with max |S| and f_hat(S) != 0 (DEG_WITNESS)
  -- 2. Find restriction with top coefficient != 0 (EXIST_TOP)
  -- 3. Apply full-degree theorem (FULLCASE)
  -- 4. Lift via sensitivity_restriction_le (SENS_MONO)
  ...`}
          </LeanCode>
          <div className="mt-6">
            <Latex display>{"\\therefore\\; s(f) \\geq \\sqrt{\\deg(f)} \\quad \\blacksquare"}</Latex>
          </div>
        </div>

        <div className="bg-white p-6 rounded-lg primer-border mt-8">
          <h4 className="primer-heading text-lg mb-3">Historical Note</h4>
          <p>
            The Sensitivity Conjecture was open for nearly 30 years before Huang's 2019 proof.
            The key insight — using a signed version of the adjacency matrix — reduced a
            combinatorial problem to a clean spectral argument. The proof is now a masterclass
            in the power of choosing the right representation.
          </p>
        </div>

        <div className="bg-primer-gold-light p-6 rounded-lg mt-8">
          <h4 className="primer-heading text-lg mb-3">The Lean Formalization</h4>
          <p>
            This primer follows the structure of the Lean formalization, which provides
            machine-checked verification of every step. The key atoms in the proof DAG:
          </p>
          <ul className="mt-4 space-y-1 text-sm font-mono">
            <li>BC0-BC4: Boolean cube definitions</li>
            <li>SEN0: Sensitivity definition</li>
            <li>CHI0: Parity characters</li>
            <li>FOURIER0, DEG0: Fourier coefficients and degree</li>
            <li>GVAL0, LEVELSETS: g-transform and level sets</li>
            <li>HUANG_DEF, HUANG_SPEC: Huang matrix and spectrum</li>
            <li>INTERLACE, SPEC_UPPER: Spectral bounds</li>
            <li>FULLCASE: Full-degree theorem</li>
            <li>REDUCE: Restriction argument</li>
            <li>GOAL: Final theorem</li>
          </ul>
        </div>
      </div>
    </SectionWrapper>
  );
}

// ============================================================================
// LEAN SYNTAX HIGHLIGHTER
// ============================================================================

interface LeanToken {
  type: 'keyword' | 'type' | 'function' | 'comment' | 'string' | 'number' | 'operator' | 'punctuation' | 'tactic' | 'text';
  content: string;
}

function tokenizeLean(code: string): LeanToken[] {
  const tokens: LeanToken[] = [];
  const keywords = ['def', 'theorem', 'lemma', 'by', 'match', 'with', 'if', 'then', 'else', 'let', 'have', 'exact', 'intro', 'intros', 'rfl', 'simp', 'aesop', 'cases', 'induction', 'apply', 'refine', 'constructor', 'obtain', 'fun', 'where', 'noncomputable', 'section', 'end', 'open', 'import', 'set_option', 'namespace', 'classical', 'ext', 'conv', 'rw', 'unfold', 'generalize_proofs'];
  const types = ['Nat', 'ℕ', 'Bool', 'Prop', 'Type', 'Type*', 'ℝ', 'Real', 'Matrix', 'Finset', 'Fin', 'List', 'Set', 'Equiv', 'Module', 'Submodule', 'SimpleGraph', 'OrthonormalBasis', 'EuclideanSpace'];
  const tactics = ['simp_all', 'norm_num', 'positivity', 'grind', 'tauto', 'ring', 'field_simp', 'linarith', 'decide', 'assumption'];

  let i = 0;
  while (i < code.length) {
    // Comments
    if (code.slice(i, i + 2) === '/-') {
      let end = code.indexOf('-/', i + 2);
      if (end === -1) end = code.length;
      else end += 2;
      tokens.push({ type: 'comment', content: code.slice(i, end) });
      i = end;
      continue;
    }
    if (code.slice(i, i + 2) === '--') {
      let end = code.indexOf('\n', i);
      if (end === -1) end = code.length;
      tokens.push({ type: 'comment', content: code.slice(i, end) });
      i = end;
      continue;
    }

    // Strings
    if (code[i] === '"') {
      let end = i + 1;
      while (end < code.length && code[end] !== '"') {
        if (code[end] === '\\') end++;
        end++;
      }
      tokens.push({ type: 'string', content: code.slice(i, end + 1) });
      i = end + 1;
      continue;
    }

    // Numbers
    if (/\d/.test(code[i])) {
      let end = i;
      while (end < code.length && /[\d.]/.test(code[end])) end++;
      tokens.push({ type: 'number', content: code.slice(i, end) });
      i = end;
      continue;
    }

    // Operators and special symbols
    if ('+-*/^≥≤≠=<>∧∨¬∀∃∈∉⊆⊂⊇⊃∩∪∅→←↔⟨⟩•·'.includes(code[i])) {
      tokens.push({ type: 'operator', content: code[i] });
      i++;
      continue;
    }

    // Punctuation
    if ('()[]{}:;,.'.includes(code[i])) {
      tokens.push({ type: 'punctuation', content: code[i] });
      i++;
      continue;
    }

    // Identifiers and keywords
    if (/[a-zA-Z_α-ωΑ-Ω']/.test(code[i])) {
      let end = i;
      while (end < code.length && /[a-zA-Z0-9_α-ωΑ-Ω'₀-₉]/.test(code[end])) end++;
      const word = code.slice(i, end);

      if (keywords.includes(word)) {
        tokens.push({ type: 'keyword', content: word });
      } else if (types.includes(word)) {
        tokens.push({ type: 'type', content: word });
      } else if (tactics.includes(word)) {
        tokens.push({ type: 'tactic', content: word });
      } else {
        tokens.push({ type: 'text', content: word });
      }
      i = end;
      continue;
    }

    // Whitespace and other
    tokens.push({ type: 'text', content: code[i] });
    i++;
  }

  return tokens;
}

function HighlightedLean({ code, highlightLines }: { code: string; highlightLines?: [number, number] }) {
  const lines = code.split('\n');

  return (
    <pre className="text-sm font-mono leading-relaxed">
      {lines.map((line, lineIdx) => {
        const isHighlighted = highlightLines &&
          lineIdx >= highlightLines[0] &&
          lineIdx <= highlightLines[1];
        const tokens = tokenizeLean(line);

        return (
          <div
            key={lineIdx}
            className={`px-2 ${isHighlighted ? 'bg-primer-gold/20 border-l-4 border-primer-gold' : ''}`}
          >
            <span className="inline-block w-10 text-stone-400 text-right mr-4 select-none">
              {lineIdx + 1}
            </span>
            {tokens.map((token, tokenIdx) => {
              const colorClass = {
                keyword: 'text-purple-600 font-semibold',
                type: 'text-blue-600',
                function: 'text-amber-600',
                comment: 'text-stone-400 italic',
                string: 'text-green-600',
                number: 'text-orange-500',
                operator: 'text-rose-500',
                punctuation: 'text-stone-500',
                tactic: 'text-teal-600 font-medium',
                text: 'text-stone-800',
              }[token.type];

              return (
                <span key={tokenIdx} className={colorClass}>
                  {token.content}
                </span>
              );
            })}
          </div>
        );
      })}
    </pre>
  );
}

// ============================================================================
// LEAN PROOF SECTIONS DATA
// ============================================================================

interface LeanSection {
  id: string;
  title: string;
  description: string;
  sectionNumber: number; // 1-24, used to load MDX content
  lineStart: number;
  lineEnd: number;
}

// Full Lean code organized by section with detailed explanations
const leanSections: LeanSection[] = [
  {
    id: "core-definitions",
    title: "Core definitions",
    description: "Sensitivity, Fourier coefficients, and degree for Boolean functions.",
    sectionNumber: 1,
    lineStart: 0,
    lineEnd: 280,
  },
  {
    id: "equivalences-huang",
    title: "Equivalences and Huang matrix definition",
    description: "Type equivalences for reindexing and the recursive definition of the Huang matrix.",
    sectionNumber: 2,
    lineStart: 281,
    lineEnd: 359,
  },
  {
    id: "spectral-prelim",
    title: "Spectral preliminaries",
    description: "A² = nI, eigenvalue characterization, and min-max eigenvalue theory.",
    sectionNumber: 3,
    lineStart: 360,
    lineEnd: 561,
  },
  {
    id: "huang-reindex",
    title: "Huang matrix reindexing and eigen-structure",
    description: "Reindexing to Fin(2^n), g-transform expectation, and complete spectrum.",
    sectionNumber: 4,
    lineStart: 562,
    lineEnd: 854,
  },
  {
    id: "spectral-bounds",
    title: "Spectral bounds and interlacing",
    description: "Rayleigh quotients, Courant-Fischer, eigenvalue interlacing, and submatrix bounds.",
    sectionNumber: 5,
    lineStart: 855,
    lineEnd: 1367,
  },
  {
    id: "level-sets",
    title: "Level-set combinatorics",
    description: "The g-transform, level sets S⁺ and S⁻, and why one must be large.",
    sectionNumber: 6,
    lineStart: 1368,
    lineEnd: 1470,
  },
  {
    id: "hypercube-graph",
    title: "Hypercube graph and adjacency bridge",
    description: "The hypercube graph Q_n and its connection to the Huang matrix and sensitivity.",
    sectionNumber: 7,
    lineStart: 1471,
    lineEnd: 1683,
  },
  {
    id: "full-degree",
    title: "Full-degree case (core bound)",
    description: "Restriction to subcubes, sensitivity monotonicity, and the final theorem.",
    sectionNumber: 8,
    lineStart: 1684,
    lineEnd: 2163,
  },
];

// The actual Lean code to display
const fullLeanCode = `import Mathlib

import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic \`generalize_proofs\` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName \`pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let \`(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-
The sensitivity of a boolean function f is the maximum over all inputs x of the number of neighbors y of x such that f(x) ≠ f(y).
-/
def sensitivity {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup Finset.univ (fun x => Finset.card (Finset.filter (fun y => (Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y) Finset.univ))

/-
chi_S(x) is (-1)^(x \cdot S), which is 1 if the number of indices in S where x is true is even, and -1 otherwise.
-/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  if (Finset.filter (fun i => x i) S).card % 2 = 0 then 1 else -1

/-
The Fourier coefficient f_hat(S) is the expectation of f(x) * chi_S(x). The degree of f is the size of the largest set S such that f_hat(S) is non-zero.
-/
noncomputable def fourier_coeff {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (Finset.sum Finset.univ (fun x => (if f x then 1 else 0) * chi S x)) / 2^n

noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.sup (Finset.filter (fun S => fourier_coeff f S ≠ 0) Finset.univ) Finset.card

/-
Equivalence between Bool x alpha and alpha + alpha.
-/
def boolProdEquivSum_custom {α : Type*} : Bool × α ≃ α ⊕ α where
  toFun := fun p => if p.1 then Sum.inr p.2 else Sum.inl p.2
  invFun := fun s => match s with
    | Sum.inl a => (false, a)
    | Sum.inr a => (true, a)
  left_inv := by
    rintro ⟨ _ | _, _ ⟩ <;> simp +decide
  right_inv := by
    rintro (a | a) <;> rfl

/-
Equivalence between functions from Fin (n+1) to alpha and pairs of (alpha, function from Fin n to alpha).
-/
def finSuccEquiv_custom (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, f ∘ Fin.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp

/-
Equivalence between functions from Fin (n+1) to Bool and the sum of two copies of functions from Fin n to Bool.
-/
def finSuccEquiv_huang_custom (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) :=
  Equiv.trans
    (finSuccEquiv_custom n Bool)
    (boolProdEquivSum_custom)

/-
The Huang matrix A_n is defined recursively. A_0 is 0. A_{n+1} is a block matrix with A_n on the diagonal, I on the off-diagonal, and -A_n on the other diagonal, reindexed to match the boolean hypercube indices.
-/
def huang_matrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  match n with
  | 0 => 0
  | n + 1 => Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm
      (Matrix.fromBlocks (huang_matrix n) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix n))

/-
The square of the Huang matrix A_n is n times the identity matrix.
-/
theorem huang_matrix_sq (n : ℕ) : (huang_matrix n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  induction' n with n ih;
  · norm_num [ sq ];
    exact mul_eq_zero_of_left rfl (huang_matrix 0)
  · -- By definition of huang_matrix, we have:
    have h_def : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    -- By definition of matrix multiplication and the induction hypothesis, we can expand the square of the block matrix.
    have h_expand : (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) ^ 2 = Matrix.fromBlocks ((n + 1 : ℝ) • 1) 0 0 ((n + 1 : ℝ) • 1) := by
      simp_all +decide [ sq, Matrix.fromBlocks_multiply ];
      norm_num [ add_smul, add_comm ];
    simp_all +decide [ sq, Matrix.reindex_apply ];
    ext i j; simp +decide [ Matrix.submatrix, Matrix.smul_eq_diagonal_mul ] ;
    by_cases hij : i = j <;> simp +decide [ hij, Matrix.one_apply ]

/-
The eigenvalues of the Huang matrix square to n.
-/
theorem huang_matrix_eigenvalues {n : ℕ} {μ : ℝ} (h : Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix n)) μ) : μ ^ 2 = n := by
  obtain ⟨ v, hv ⟩ := h.exists_hasEigenvector;
  -- Since $A^2 = nI$, we have $A^2 v = n v$.
  have h_sq : (Matrix.toLin' (huang_matrix n)) (Matrix.toLin' (huang_matrix n) v) = (n : ℝ) • v := by
    convert congr_arg ( fun x : Matrix ( Fin n → Bool ) ( Fin n → Bool ) ℝ => x.mulVec v ) <| huang_matrix_sq n using 1;
    · simp +decide [ sq ];
    · simp +decide [ Matrix.smul_eq_diagonal_mul ];
  -- Since $v$ is an eigenvector of $A$, we have $A v = \mu v$.
  have h_eigen : (Matrix.toLin' (huang_matrix n)) v = μ • v := by
    cases hv ; aesop;
  simp_all +decide [ sq ];
  exact smul_left_injective _ hv.2 <| by simpa [ mul_assoc, smul_smul ] using h_sq;

/-
The sorted list of eigenvalues of a real matrix, defined as the sorted roots of its characteristic polynomial.
-/
noncomputable def sorted_eigenvalues_list {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (A.charpoly.roots).sort (· ≤ ·)

/-
A predicate asserting that list M interlaces list L.
-/
def interlacing (L M : List ℝ) : Prop :=
  L.length = M.length + 1 ∧
  ∀ i : Fin M.length, L[i]! ≤ M[i]! ∧ M[i]! ≤ L[i.1 + 1]!

/-
A real matrix is symmetric if and only if it is Hermitian.
-/
theorem isSymm_iff_isHermitian_real {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
  A.IsSymm ↔ A.IsHermitian := by
  rw [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
  simp
  rfl

/-
The sorted eigenvalues of a symmetric matrix.
-/
noncomputable def sorted_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : List ℝ :=
  let hA' : A.IsHermitian := (isSymm_iff_isHermitian_real A).mp hA
  (List.ofFn (hA'.eigenvalues)).mergeSort (· ≤ ·)

/-
The number of sorted eigenvalues is n.
-/
theorem sorted_eigenvalues_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).length = n := by
    unfold sorted_eigenvalues; aesop;

/-
For a symmetric matrix A, <Ax, y> = <x, Ay>.
-/
theorem dotProduct_mulVec_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x y : Fin n → ℝ) :
  dotProduct (A.mulVec x) y = dotProduct x (A.mulVec y) := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_comm];
    rw [ Finset.sum_comm ];
    conv_rhs => rw [ ← hA ] ;
    rfl

/-
The max-min value for the k-th eigenvalue.
-/
def min_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ⨆ (C : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ C = k + 1),
    ⨅ (x : {x : C // dotProduct (x : Fin n → ℝ) (x : Fin n → ℝ) = 1}),
      dotProduct (A.mulVec (x : Fin n → ℝ)) (x : Fin n → ℝ)

/-
The sorted eigenvalues are a permutation of the eigenvalues.
-/
lemma sorted_eigenvalues_is_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n),
    (sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩ =
    Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) (σ i) := by
      classical
      -- Since L and M are permutations, there is a permutation of indices matching their entries.
      have h_perm : ∀ (L M : List ℝ), List.Perm L M →
          ∃ σ : Fin L.length ≃ Fin M.length, ∀ i : Fin L.length, L.get i = M.get (σ i) := by
        intro L M h_perm
        induction h_perm with
        | nil =>
            refine ⟨Equiv.refl _, ?_⟩
            intro i
            exact (Fin.elim0 i)
        | cons a h_perm ih =>
            rename_i L' M'
            obtain ⟨σ, hσ⟩ := ih
            let f : Fin (L'.length + 1) → Fin (M'.length + 1) :=
              fun i => Fin.cases ⟨0, by simp⟩ (fun i => Fin.succ (σ i)) i
            have hf_inj : Function.Injective f := by
              intro i j hij
              cases i using Fin.cases with
              | zero =>
                  cases j using Fin.cases with
                  | zero => rfl
                  | succ j =>
                      simp [f] at hij
                      exact (Fin.succ_ne_zero _ (Eq.symm hij)).elim
              | succ i =>
                  cases j using Fin.cases with
                  | zero =>
                      simp [f] at hij
                      -- goal is closed by simp
                  | succ j =>
                      simp [f] at hij
                      exact congrArg Fin.succ hij
            have hf_surj : Function.Surjective f := by
              intro j
              cases j using Fin.cases with
              | zero =>
                  refine ⟨⟨0, by simp⟩, ?_⟩
                  simp [f]
              | succ j =>
                  refine ⟨Fin.succ (σ.symm j), ?_⟩
                  simp [f]
            let σ' : Fin (L'.length + 1) ≃ Fin (M'.length + 1) :=
              Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
            refine ⟨σ', ?_⟩
            intro i
            cases i using Fin.cases with
            | zero =>
                simp [σ', f]
            | succ i =>
                simpa [σ', f, List.get_cons_succ'] using hσ i
        | swap a b l =>
            refine ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, ?_⟩
            intro i
            refine Fin.cases ?h0 ?hs i
            ·
              simp
            · intro i
              refine Fin.cases ?h1 ?hrest i
              ·
                simp
              · intro j
                have hne0 : (Fin.succ (Fin.succ j) : Fin (l.length + 2)) ≠ 0 := by
                  exact Fin.succ_ne_zero _
                have hne1 : (Fin.succ (Fin.succ j) : Fin (l.length + 2)) ≠ 1 := by
                  exact Fin.succ_succ_ne_one _
                simp [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
        | trans h₁ h₂ ih₁ ih₂ =>
            obtain ⟨σ₁, hσ₁⟩ := ih₁
            obtain ⟨σ₂, hσ₂⟩ := ih₂
            refine ⟨σ₁.trans σ₂, ?_⟩
            intro i
            exact (hσ₁ i).trans (hσ₂ (σ₁ i))
      generalize_proofs at *
      -- Apply the permutation property to the sorted eigenvalues and the original eigenvalues.
      obtain ⟨σ, hσ⟩ :
          ∃ σ : Fin n ≃ Fin n,
            ∀ i : Fin n,
              (sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩ =
                (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)) (σ i) := by
        have h_perm_list :
            List.Perm (sorted_eigenvalues A hA)
              (List.ofFn (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA))) := by
          unfold sorted_eigenvalues
          generalize_proofs at *
          simpa using
            (List.mergeSort_perm
              (List.ofFn (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)))
              (· ≤ ·))
        rcases h_perm _ _ h_perm_list with ⟨σ, hσ⟩
        let f := Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)
        have hlenL : (sorted_eigenvalues A hA).length = n := sorted_eigenvalues_length A hA
        have hlenM : (List.ofFn f).length = n := by
          simp
        -- transport σ to a permutation on Fin n using the length equalities
        let σ' : Fin n ≃ Fin n :=
          (finCongr hlenL.symm).trans (σ.trans (finCongr hlenM))
        refine ⟨σ', ?_⟩
        intro i
        let iL : Fin (sorted_eigenvalues A hA).length := finCongr hlenL.symm i
        have hidx :
            (⟨i, by
                simp [sorted_eigenvalues_length]⟩ :
              Fin (sorted_eigenvalues A hA).length) = iL := by
          apply Fin.ext
          rfl
        have hσi := hσ iL
        simpa [σ', iL, hidx, f, List.get_ofFn] using hσi
      exact ⟨σ, hσ⟩

/-
There exists an orthonormal basis of eigenvectors corresponding to the sorted eigenvalues.
-/
lemma exists_orthonormal_basis_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  ∃ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
    ∀ i, A.mulVec (v i) = ((sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩) • (v i) := by
      have h_eigen_decomp : ∃ (σ : Equiv.Perm (Fin n)), ∀ i : Fin n, Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) (σ i) = (sorted_eigenvalues A hA).get ⟨i, by
        rw [ sorted_eigenvalues_length ] ; exact i.2⟩ := by
        have := sorted_eigenvalues_is_perm A hA
        generalize_proofs at *;
        exact ⟨ this.choose, fun i => this.choose_spec i ▸ rfl ⟩
      generalize_proofs at *;
      obtain ⟨ σ, hσ ⟩ := h_eigen_decomp
      generalize_proofs at *;
      -- By the properties of the spectral theorem, there exists an orthonormal basis of eigenvectors corresponding to the eigenvalues.
      obtain ⟨v, hv⟩ : ∃ v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i : Fin n, A.mulVec (v i) = Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) i • v i := by
        exact ⟨ Matrix.IsHermitian.eigenvectorBasis ( by tauto ), fun i => by simpa using Matrix.IsHermitian.mulVec_eigenvectorBasis ( by tauto ) i ⟩;
      refine' ⟨ v.reindex σ.symm, fun i => _ ⟩ ; aesop

/-
The inner product in EuclideanSpace is the dot product.
-/
lemma inner_eq_dotProduct {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
  inner ℝ x y = dotProduct (x : Fin n → ℝ) (y : Fin n → ℝ) := by
    simp +decide [ dotProduct, inner ];
    ac_rfl

/-
$\EE(g) \neq 0$
-/
theorem g_expectation_nonzero {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  let g := fun x => (if f x then 1 else 0) * chi Finset.univ x
  (Finset.sum Finset.univ g) ≠ 0 := by
    have h_fourier_coeff : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ S.card = n := by
      contrapose! h_deg;
      refine' ne_of_lt ( lt_of_le_of_lt ( Finset.sup_le _ ) _ );
      exacts [ n - 1, fun S hS => Nat.le_sub_one_of_lt <| lt_of_le_of_ne ( le_trans ( Finset.card_le_univ _ ) <| by simp ) <| h_deg S <| by simpa using hS, Nat.pred_lt hn ];
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_fourier_coeff; simp_all +decide [ fourier_coeff ] ;
    have := Finset.eq_of_subset_of_card_le ( Finset.subset_univ S ) ; aesop;

/-
Equivalence between boolean functions and Fin (2^n).
-/
def boolFunEquivFin (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Fintype.equivFin (Fin n → Bool)).trans (finCongr (by
  norm_num [ Fintype.card_pi ]))

/-
Reindexing of Huang matrix to Fin (2^n).
-/
noncomputable def huang_matrix_fin (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℝ :=
  Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)

/-
The Huang matrix is symmetric.
-/
theorem huang_matrix_isSymm (n : ℕ) : (huang_matrix n).IsSymm := by
  induction' n with n ih;
  · exact rfl
  · -- By definition of huang_matrix, we know that huang_matrix (n + 1) is a block matrix with huang_matrix n on the diagonal, I on the off-diagonal, and -huang_matrix n on the other diagonal, reindexed to match the boolean hypercube indices.
    have h_block : huang_matrix (n + 1) = Matrix.reindex (finSuccEquiv_huang_custom n).symm (finSuccEquiv_huang_custom n).symm (Matrix.fromBlocks (huang_matrix n) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huang_matrix n)) := by
      rfl;
    simp_all +decide [ Matrix.IsSymm ];
    ext i j; simp +decide [ Matrix.fromBlocks_transpose, ih ] ;

/-
The reindexed Huang matrix is symmetric.
-/
theorem huang_matrix_fin_isSymm (n : ℕ) : (huang_matrix_fin n).IsSymm := by
  exact funext fun i => funext fun j => huang_matrix_isSymm n |>.apply _ _

/-
The square of the reindexed Huang matrix is n*I.
-/
theorem huang_matrix_fin_sq (n : ℕ) : (huang_matrix_fin n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℝ) := by
  ext i j;
  simp +decide [ huang_matrix_fin, sq ];
  convert congr_fun ( congr_fun ( huang_matrix_sq n ) ( ( boolFunEquivFin n ).symm i ) ) ( ( boolFunEquivFin n ).symm j ) using 1 ; norm_num [ Matrix.mul_apply ];
  · rw [ sq, Matrix.mul_apply ];
  · simp +decide [ Matrix.one_apply, Matrix.smul_apply ]

/-
The trace of the Huang matrix is 0.
-/
theorem huang_matrix_trace (n : ℕ) : Matrix.trace (huang_matrix n) = 0 := by
  induction n <;> simp_all +decide [ Matrix.trace ];
  · rfl;
  · rename_i n ih; rw [ show ( huang_matrix ( n + 1 ) ) = Matrix.reindex ( finSuccEquiv_huang_custom n ).symm ( finSuccEquiv_huang_custom n ).symm ( Matrix.fromBlocks ( huang_matrix n ) ( 1 : Matrix _ _ ℝ ) ( 1 : Matrix _ _ ℝ ) ( -huang_matrix n ) ) by rfl ] ; simp +decide ;
    unfold finSuccEquiv_huang_custom;
    unfold finSuccEquiv_custom boolProdEquivSum_custom; simp +decide [ Matrix.fromBlocks ] ;
    rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.cons true x ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.cons false x ) Finset.univ from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, ih ];
    · rw [ neg_add_eq_zero ];
      exact rfl
    · norm_num [ Finset.disjoint_left ];
    · ext x; simp +decide ;
      exact if h : x 0 then Or.inl ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩ else Or.inr ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> aesop ⟩

/-
Every eigenvalue of the Huang matrix squares to n.
-/
theorem huang_eigenvalues_sq_eq_n (n : ℕ) (i : Fin (2^n)) :
  ((sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.2⟩) ^ 2 = n := by
    -- Apply the fact that the eigenvalues of the Huang matrix square to n.
    have h_eigenvalue : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix_fin n)) μ → μ ^ 2 = n := by
      intro μ hμ
      generalize_proofs at *;
      have h_eigenvalue : μ ^ 2 = n := by
        have h_sq : (huang_matrix_fin n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℝ) := by
          exact huang_matrix_fin_sq n
        have h_eigenvalue : ∀ (v : Fin (2^n) → ℝ), v ≠ 0 → (huang_matrix_fin n).mulVec v = μ • v → μ ^ 2 = n := by
          intros v hv hμv
          have h_eigenvalue : (huang_matrix_fin n).mulVec ((huang_matrix_fin n).mulVec v) = μ ^ 2 • v := by
            rw [ hμv, Matrix.mulVec_smul, pow_two, MulAction.mul_smul ];
            rw [ hμv ]
          generalize_proofs at *;
          have h_eigenvalue : (huang_matrix_fin n).mulVec ((huang_matrix_fin n).mulVec v) = (n : ℝ) • v := by
            simp +decide [ ← sq, h_sq ];
            simp +decide [ Matrix.smul_eq_diagonal_mul ]
          generalize_proofs at *;
          exact smul_left_injective _ hv <| by aesop;
        generalize_proofs at *;
        obtain ⟨ v, hv ⟩ := hμ.exists_hasEigenvector;
        cases hv ; aesop
      generalize_proofs at *;
      exact h_eigenvalue
    generalize_proofs at *;
    -- By definition of sorted_eigenvalues, every element in the list is an eigenvalue of the matrix.
    have h_sorted_eigenvalue : ∀ μ ∈ sorted_eigenvalues (huang_matrix_fin n) ‹_›, Module.End.HasEigenvalue (Matrix.toLin' (huang_matrix_fin n)) μ := by
      unfold sorted_eigenvalues;
      simp_all +decide [ Module.End.HasUnifEigenvalue ];
      intro a; specialize h_eigenvalue ( Matrix.IsHermitian.eigenvalues ‹_› a ) ; simp_all +decide [ Submodule.eq_bot_iff ] ;
      have := Matrix.IsHermitian.eigenvectorBasis ‹_› |> OrthonormalBasis.orthonormal;
      exact ⟨ _, Matrix.IsHermitian.mulVec_eigenvectorBasis _ _, this.linearIndependent.ne_zero _ ⟩;
    aesop

/-
The sum of sorted eigenvalues is the trace.
-/
theorem sum_sorted_eigenvalues_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).sum = A.trace := by
    -- The sum of the eigenvalues of a symmetric matrix is equal to its trace.
    have h_sum_eigenvalues : (List.ofFn (Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA))).sum = Matrix.trace A := by
      -- Apply the theorem that states the trace of a matrix is equal to the sum of its eigenvalues.
      have h_trace_eq_sum_eigenvalues : Matrix.trace A = ∑ i : Fin n, (Matrix.IsHermitian.eigenvalues (isSymm_iff_isHermitian_real A |>.mp hA)) i := by
        have := ( isSymm_iff_isHermitian_real A ).mp hA;
        have := this.trace_eq_sum_eigenvalues;
        exact_mod_cast this;
      rw [ h_trace_eq_sum_eigenvalues, List.sum_ofFn ];
    rw [ ← h_sum_eigenvalues ];
    unfold sorted_eigenvalues;
    rw [ List.Perm.sum_eq ( List.mergeSort_perm _ _ ) ]

/-
If a list contains only c and -c and sums to 0, then the counts are equal.
-/
lemma list_sum_zero_eq_count {c : ℝ} (hc : c ≠ 0) (L : List ℝ)
  (h_mem : ∀ x ∈ L, x = c ∨ x = -c) (h_sum : L.sum = 0) :
  L.count c = L.count (-c) := by
    -- We can split the sum into the sum of the c's and the sum of the -c's.
    have h_split_sum : ∑ x ∈ L.toFinset, x * (L.count x) = c * (L.count c) + (-c) * (L.count (-c)) := by
      field_simp;
      rw [ Finset.sum_eq_add ( c ) ( -c ) ] <;> norm_num;
      · ring;
      · exact fun h => hc <| by linarith;
      · grind;
      · exact fun h => Or.inr <| List.count_eq_zero_of_not_mem h;
      · exact fun h => Or.inr <| List.count_eq_zero_of_not_mem h;
    have h_split_sum_eq_zero : ∑ x ∈ L.toFinset, x * (L.count x) = L.sum := by
      simp +decide [ Finset.sum_list_count ];
      ac_rfl;
    exact_mod_cast ( mul_left_cancel₀ hc <| by linarith : ( L.count c : ℝ ) = L.count ( -c ) )

/-
A list of -c's followed by c's is sorted if c ≥ 0.
-/
lemma sorted_replicate_append_replicate {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
  (List.replicate m (-c) ++ List.replicate m c).Sorted (· ≤ ·) := by
    -- The list is sorted because each element in the first part is -c and each element in the second part is c, and -c ≤ c since c ≥ 0.
    simp [List.Sorted];
    rw [ List.pairwise_append ] ; aesop

/-
If a sorted list has m -c's and m c's, it is equal to m -c's followed by m c's.
-/
lemma list_eq_replicate_append_replicate {c : ℝ} (hc : 0 ≤ c) (L : List ℝ) (m : ℕ)
  (h_len : L.length = 2 * m)
  (h_count_neg : L.count (-c) = m)
  (h_count_pos : L.count c = m)
  (h_mem : ∀ x ∈ L, x = c ∨ x = -c)
  (h_sorted : L.Sorted (· ≤ ·)) :
  L = List.replicate m (-c) ++ List.replicate m c := by
    refine' List.eq_of_perm_of_sorted _ h_sorted ( sorted_replicate_append_replicate hc m );
    rw [ List.perm_iff_count ];
    intro a; by_cases ha : a = c <;> by_cases ha' : a = -c <;> simp_all +decide [ List.count_replicate ] ;
    · cases m <;> simp_all +decide [ neg_eq_iff_add_eq_zero ];
      rw [ List.eq_replicate_of_mem h_mem ] at h_count_pos ; aesop;
    · aesop;
    · exact fun h => False.elim <| ha <| by linarith;
    · rw [ List.count_eq_zero_of_not_mem fun h => by cases h_mem a h <;> tauto ] ; aesop

/-
If a list contains only c and d, their counts sum to the length.
-/
lemma list_count_add_count_eq_length {α : Type*} [DecidableEq α] {c d : α} (hcd : c ≠ d) (L : List α)
  (h_mem : ∀ x ∈ L, x = c ∨ x = d) :
  L.count c + L.count d = L.length := by
    induction' L with x xs ih;
    · rfl;
    · cases h_mem x ( by simp +decide ) <;> simp_all +decide [ List.count_cons ];
      · linarith;
      · grind

/-
Trace is invariant under reindexing.
-/
theorem trace_reindex_eq_trace {n : Type*} [Fintype n] {m : Type*} [Fintype m] [DecidableEq n] [DecidableEq m]
  (e : n ≃ m) (A : Matrix n n ℝ) :
  Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
    simp +decide [ Matrix.trace ];
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;

/-
The trace of the reindexed Huang matrix is 0.
-/
theorem huang_matrix_fin_trace (n : ℕ) : Matrix.trace (huang_matrix_fin n) = 0 := by
  -- The trace of the reindexed matrix is the same as the original matrix, which is 0 by huang_matrix_trace. Hence, we can conclude.
  have h_trace_reindex : Matrix.trace (Matrix.reindex (boolFunEquivFin n) (boolFunEquivFin n) (huang_matrix n)) = Matrix.trace (huang_matrix n) := by
    exact trace_reindex_eq_trace (boolFunEquivFin n) (huang_matrix n)
  exact h_trace_reindex.trans ( huang_matrix_trace n )

/-
sorted_eigenvalues returns a sorted list.
-/
theorem sorted_eigenvalues_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
  (sorted_eigenvalues A hA).Sorted (· ≤ ·) := by
    unfold sorted_eigenvalues;
    exact
      List.sorted_mergeSort' (fun x1 x2 => x1 ≤ x2)
        (List.ofFn (sorted_eigenvalues._proof_1 A hA).eigenvalues)

/-
Accessing an element in a list of two concatenated replicated lists.
-/
lemma list_replicate_append_replicate_get {n : ℕ} {c : ℝ} (i : Fin (2 * n)) :
  (List.replicate n (-c) ++ List.replicate n c).get ⟨i, by
    simpa [ two_mul ] using i.2⟩ = if i < n then -c else c := by
    aesop

/-
A sorted list of length 2m with elements squaring to c^2 and sum 0 is m -c's then m c's.
-/
lemma sorted_list_of_sq_eq_and_sum_zero {L : List ℝ} {c : ℝ} {m : ℕ} (hc : 0 < c)
  (h_len : L.length = 2 * m)
  (h_sq : ∀ x ∈ L, x^2 = c^2)
  (h_sum : L.sum = 0)
  (h_sorted : L.Sorted (· ≤ ·)) :
  L = List.replicate m (-c) ++ List.replicate m c := by
    -- Since every element in L is either c or -c and their sum is zero, the counts of c and -c must be equal.
    have h_count_eq : L.count c = L.count (-c) := by
      apply_rules [ list_sum_zero_eq_count ];
      · positivity;
      · exact fun x hx => eq_or_eq_neg_of_sq_eq_sq _ _ <| h_sq x hx;
    -- Since the counts of $c$ and $-c$ are equal and their sum is zero, the number of $c$'s and $-c$'s must be $m$ each.
    have h_count_m : L.count c = m ∧ L.count (-c) = m := by
      have h_count_eq : L.count c + L.count (-c) = 2 * m := by
        rw [ ← h_len, List.length_eq_countP_add_countP ];
        congr;
        rw [ List.countP_congr ] ; aesop;
        grind;
      grind;
    apply list_eq_replicate_append_replicate hc.le L m h_len;
    · exact h_count_m.2;
    · exact h_count_m.1;
    · exact fun x hx => eq_or_eq_neg_of_sq_eq_sq _ _ <| h_sq x hx;
    · assumption

/-
If a list satisfies the properties, its elements are determined.
-/
lemma list_properties_to_values {L : List ℝ} {c : ℝ} {m : ℕ} (hc : 0 < c)
  (h_len : L.length = 2 * m)
  (h_sq : ∀ x ∈ L, x^2 = c^2)
  (h_sum : L.sum = 0)
  (h_sorted : L.Sorted (· ≤ ·))
  (i : Fin (2 * m)) :
  L.get ⟨i, by rw [h_len]; exact i.2⟩ = if (i : ℕ) < m then -c else c := by
    have h_eq_replicate_append_replicate : L = List.replicate m (-c) ++ List.replicate m c := by
      exact sorted_list_of_sq_eq_and_sum_zero hc h_len h_sq h_sum h_sorted
    generalize_proofs at *; aesop;

/-
The sorted eigenvalues of A_{n+1} are 2^n copies of -sqrt(n+1) followed by 2^n copies of sqrt(n+1).
-/
lemma huang_eigenvalues_eq_list_succ (n : ℕ) :
  let evs := sorted_eigenvalues (huang_matrix_fin (n + 1)) (huang_matrix_fin_isSymm (n + 1))
  evs = List.replicate (2^n) (-Real.sqrt (n + 1)) ++ List.replicate (2^n) (Real.sqrt (n + 1)) := by
    generalize_proofs at *;
    apply sorted_list_of_sq_eq_and_sum_zero;
    · positivity;
    · rw [ sorted_eigenvalues_length ] ; norm_num [ pow_succ' ];
    · intro x hx;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hx;
      have := huang_eigenvalues_sq_eq_n ( n + 1 ) ⟨ i, by
        refine' i.2.trans_le _;
        rw [ sorted_eigenvalues_length ] ⟩
      generalize_proofs at *;
      rw [ Real.sq_sqrt <| by positivity ] ; aesop;
    · rw [ sum_sorted_eigenvalues_eq_trace, huang_matrix_fin_trace ];
    · exact (by
        expose_names
        exact sorted_eigenvalues_sorted (huang_matrix_fin (n + 1)) pf)

/-
The sorted eigenvalues of the Huang matrix.
-/
noncomputable def huang_eigenvalues (n : ℕ) : List ℝ :=
  sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)

/-
The absolute value of the Huang matrix entries is the adjacency matrix of the hypercube.
-/
theorem abs_huang_eq_adjacency (n : ℕ) (i j : Fin n → Bool) :
  |huang_matrix n i j| = if (Finset.filter (fun k => i k ≠ j k) Finset.univ).card = 1 then 1 else 0 := by
    rcases n with ( _ | n );
    · aesop;
    · -- By induction on $n$, we can show that the absolute value of the entries of the Huang matrix is the adjacency matrix of the hypercube.
      have h_ind : ∀ n : ℕ, ∀ i j : Fin (n + 1) → Bool, |(huang_matrix (n + 1)) i j| = if (Finset.card (Finset.filter (fun k => i k ≠ j k) Finset.univ)) = 1 then 1 else 0 := by
        -- We proceed by induction on $n$.
        intro n
        induction' n with n ih;
        · simp +decide [ huang_matrix ];
          intro i j; fin_cases i <;> fin_cases j <;> simp +decide [ finSuccEquiv_huang_custom ] ;
          · rfl;
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · simp +decide [ boolProdEquivSum_custom, finSuccEquiv_custom ];
            simp +decide [ Matrix.one_apply ];
          · rfl;
        · intro i j;
          -- By definition of \`huang_matrix\`, we can split into cases based on whether \`i\` and \`j\` are in the same block or different blocks.
          have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
            intros i j;
            have h_split : ∀ i j : Fin (n + 2) → Bool, |(huang_matrix (n + 2)) i j| = if (i 0 = j 0) then |(huang_matrix (n + 1)) (fun k => i (Fin.succ k)) (fun k => j (Fin.succ k))| else if (Finset.card (Finset.filter (fun k => i (Fin.succ k) ≠ j (Fin.succ k)) Finset.univ)) = 0 then 1 else 0 := by
              intro i j
              have h_def : huang_matrix (n + 2) = Matrix.reindex (finSuccEquiv_huang_custom (n + 1)).symm (finSuccEquiv_huang_custom (n + 1)).symm (Matrix.fromBlocks (huang_matrix (n + 1)) (1 : Matrix _ _ ℝ) (1 : Matrix _ _ ℝ) (-huang_matrix (n + 1))) := by
                exact rfl
              simp +decide [ h_def, Matrix.fromBlocks ];
              unfold finSuccEquiv_huang_custom;
              unfold finSuccEquiv_custom; simp +decide ;
              unfold boolProdEquivSum_custom; simp +decide ;
              split_ifs <;> simp +decide [ *, Matrix.one_apply ];
              all_goals simp_all +decide [ funext_iff ];
            exact h_split i j;
          rw [ show ( Finset.univ.filter fun k => i k ≠ j k ) = if i 0 = j 0 then Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) else Finset.image ( Fin.succ ) ( Finset.univ.filter fun k => i ( Fin.succ k ) ≠ j ( Fin.succ k ) ) ∪ { 0 } from ?_ ];
          · split_ifs <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
          · ext ( _ | k ) <;> simp +decide;
            · split_ifs <;> simp +decide [ * ];
            · split_ifs <;> simp_all +decide [ Finset.mem_image, Finset.mem_insert ];
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, ha, ha' ⟩ ; cases a ; aesop ⟩;
              · exact ⟨ fun h => ⟨ ⟨ k, by linarith ⟩, h, rfl ⟩, by rintro ⟨ a, h, ha ⟩ ; cases a ; aesop ⟩;
      exact h_ind n i j

/-
The sorted eigenvalues of the Huang matrix A_n (for n > 0) are 2^(n-1) copies of -sqrt(n) and 2^(n-1) copies of sqrt(n).
-/
theorem huang_eigenvalues_eq_list (n : ℕ) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
  evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
    induction' n with n ih;
    · contradiction;
    · convert huang_eigenvalues_eq_list_succ n using 1;
      norm_cast

/-
Any eigenvalue of a real matrix is bounded in absolute value by the maximum absolute row sum.
-/
theorem eigenvalue_le_max_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
  (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
  ∃ i : Fin n, |μ| ≤ Finset.sum Finset.univ (fun j => |A i j|) := by
    -- Let v be a nonzero eigenvector. Let i be the index maximizing |v_i|.
    obtain ⟨v, hv⟩ : ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v := by
      obtain ⟨ v, hv ⟩ := hμ.exists_hasEigenvector;
      cases hv ; aesop
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ∀ j : Fin n, |v j| ≤ |v i| := by
      have := Finset.exists_max_image Finset.univ ( fun i => |v i| ) ⟨ ⟨ 0, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Finset.mem_univ _ ⟩ ; aesop;
    -- Then |μ v_i| = |(Av)_i| = |sum_j A_ij v_j| ≤ sum_j |A_ij| |v_j| ≤ sum_j |A_ij| |v_i| = |v_i| sum_j |A_ij|.
    have h_bound : |μ * v i| ≤ |v i| * ∑ j, |A i j| := by
      have h_bound : |μ * v i| = |∑ j, A i j * v j| := by
        have := congr_fun hv.2 i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      rw [ h_bound, Finset.mul_sum _ _ _ ];
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, mul_comm ] ; exact mul_le_mul_of_nonneg_right ( hi j ) ( abs_nonneg _ ) );
    exact ⟨ i, by
      rw [ abs_mul ] at h_bound
      refine le_of_not_gt ?_
      intro hi'
      have hvipos : 0 < |v i| := by
        apply abs_pos.mpr
        intro hi''
        exact hv.1 <| funext fun j => by simpa [ hi'' ] using hi j
      have hgtmul : |μ| * |v i| > |v i| * ∑ j, |A i j| := by
        nlinarith [hi', hvipos]
      exact (not_le_of_gt hgtmul) h_bound ⟩

/-
Checking Fintype.card_coe
-/
/-
The largest eigenvalue of a symmetric matrix is bounded by the maximum degree of the graph defined by its non-zero entries.
-/
theorem spectral_radius_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (G : SimpleGraph (Fin n))
  (h_adj : ∀ i j, |A i j| ≤ if G.Adj i j then 1 else 0) (hn : n ≠ 0) :
  let evs := sorted_eigenvalues A hA
  let lambda_max := evs.getLast (List.ne_nil_of_length_pos (by rw [sorted_eigenvalues_length A hA]; exact Nat.pos_of_ne_zero hn))
  lambda_max ≤ G.maxDegree := by
    -- Since the largest eigenvalue is bounded by the maximum degree of the graph (from Lemma~\ref{lem:eigenvalue_le_max_row_sum}), we have:
    have h_bound : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ ≤ G.maxDegree := by
      intro μ hμ
      obtain ⟨i, hi⟩ := eigenvalue_le_max_row_sum A μ hμ;
      -- Since $|A i j| \leq 1$ if $G.Adj i j$ and $0$ otherwise, we have $\sum j, |A i j| \leq \sum j in G.neighborFinset i, 1$.
      have h_sum_le_neighbor : ∑ j, |A i j| ≤ ∑ j ∈ G.neighborFinset i, 1 := by
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_adj _ _ ) ( by simp +decide [ SimpleGraph.neighborFinset_def ] );
      exact le_trans ( le_abs_self μ ) ( hi.trans <| h_sum_le_neighbor.trans <| mod_cast by simpa using G.degree_le_maxDegree i );
    have h_sorted : ∀ μ ∈ sorted_eigenvalues A hA, μ ≤ G.maxDegree := by
      intros μ hμ
      obtain ⟨i, hi⟩ : ∃ i : Fin n, μ = Matrix.IsHermitian.eigenvalues ((isSymm_iff_isHermitian_real A).mp hA) i := by
        unfold sorted_eigenvalues at hμ; aesop;
      convert h_bound μ ?_;
      have := ( Matrix.IsHermitian.eigenvalues_eq hA );
      simp_all +decide [ Module.End.HasUnifEigenvalue ];
      simp_all +decide [ Submodule.eq_bot_iff ];
      exact ⟨ _, by simpa [ this ] using Matrix.IsHermitian.mulVec_eigenvectorBasis hA i, by simpa [ this ] using ( Matrix.IsHermitian.eigenvectorBasis hA ).orthonormal.ne_zero i ⟩;
    exact h_sorted _ <| List.getLast_mem _

/-
The Rayleigh quotient of a vector x with respect to a matrix A is <x, Ax> / <x, x>.
-/
def rayleigh_quotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A.mulVec x) / dotProduct x x

/-
The Courant-Fischer Min-Max value (Inf-Sup) for the k-th eigenvalue.
-/
def courant_fischer_inf_sup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  ⨅ (V : Submodule ℝ (Fin n → ℝ)) (_ : Module.finrank ℝ V = k + 1),
    ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1

/-
The Rayleigh quotient is invariant under reindexing.
-/
lemma rayleigh_quotient_reindex {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n ≃ Fin m) (x : Fin n → ℝ) :
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex e e A) (x ∘ e.symm) := by
    unfold rayleigh_quotient;
    simp +decide [ Matrix.mulVec, dotProduct ];
    simp +decide only [← Equiv.sum_comp e];
    simp +decide

/-
The Rayleigh quotient of a zero-padded vector is equal to the Rayleigh quotient of the original vector with respect to the submatrix.
-/
lemma rayleigh_quotient_submatrix_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
  (equiv : {x // x ∈ S} ≃ Fin S.card)
  (y : Fin S.card → ℝ) :
  let x : Fin n → ℝ := fun i => if h : i ∈ S then y (equiv ⟨i, h⟩) else 0
  rayleigh_quotient A x = rayleigh_quotient (Matrix.reindex equiv equiv (A.submatrix Subtype.val Subtype.val)) y := by
    -- By definition of $x$, we can split the sum into two parts: one over $S$ and one over the complement of $S$.
    simp [rayleigh_quotient];
    congr 1;
    · simp +decide [ dotProduct, Matrix.mulVec ];
      -- By reindexing the sums using the equivalence \`equiv\`, we can show that the two expressions are equal.
      have h_reindex : ∑ x : Fin n, (if h : x ∈ S then y (equiv ⟨x, h⟩) * ∑ x_1 : Fin n, (if h : x_1 ∈ S then A x x_1 * y (equiv ⟨x_1, h⟩) else 0) else 0) = ∑ x : S, y (equiv x) * ∑ x_1 : S, A x x_1 * y (equiv x_1) := by
        rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
        · rw [ ← Finset.sum_coe_sort ];
          simp +decide;
          refine' Finset.sum_congr rfl fun x hx => congr_arg _ _;
          rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> aesop;
          · aesop;
        · aesop;
      convert h_reindex using 1;
      conv_rhs => rw [ ← Equiv.sum_comp equiv.symm ] ;
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ ← Equiv.sum_comp equiv ] ; aesop;
    · simp +decide [ dotProduct ];
      rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
      · rw [ ← Finset.sum_attach ];
        rw [ ← Equiv.sum_comp equiv ] ; aesop;
      · aesop

/-
If a vector lies in the span of the eigenvectors corresponding to eigenvalues $\ge \alpha_k$, its Rayleigh quotient is at least $\alpha_k$.
-/
lemma rayleigh_ge_of_mem_span_top {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (k : Fin n)
  (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
  (hv : ∀ i, A.mulVec (v i) = ((sorted_eigenvalues A hA).get ⟨i, by rw [sorted_eigenvalues_length]; exact i.isLt⟩) • (v i))
  (x : EuclideanSpace ℝ (Fin n))
  (hx : x ∈ Submodule.span ℝ (Set.range (fun i : {j : Fin n // k ≤ j} => v i)))
  (hx0 : x ≠ 0) :
  rayleigh_quotient A x ≥ (sorted_eigenvalues A hA).get ⟨k, by rw [sorted_eigenvalues_length]; exact k.isLt⟩ := by
    classical
    set ev := sorted_eigenvalues A hA
    have hv' : ∀ i, A.mulVec (v i) = (ev.get ⟨i, by simp [ev, sorted_eigenvalues_length]⟩) • v i := by
      simpa [ev] using hv
    -- Let $x = \sum_{i \in K} c_i v_i$ be the decomposition of $x$ in the orthonormal basis $v$.
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i : Fin n, c i • v i ∧ ∀ i : Fin n, i < k → c i = 0 := by
      -- By definition of submodule span, there exists a finite subset of the basis vectors that spans x.
      obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i : Fin n, c i • v i ∧ ∀ i : Fin n, i < k → c i = 0 := by
        have h_span : x ∈ Submodule.span ℝ (Set.range (fun i : Fin n => if i < k then 0 else v i)) := by
          refine' Submodule.span_le.mpr _ hx;
          rintro _ ⟨ i, rfl ⟩ ; by_cases hi : ( i : Fin n ) < k <;> simp +decide;
          · exfalso; exact (not_le_of_gt hi) i.2;
          · exact Submodule.subset_span ⟨ i, by aesop ⟩
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
        obtain ⟨ c, hc ⟩ := h_span; use fun i => if i < k then 0 else c i; simp_all +decide [ Finsupp.sum_fintype ] ;
      use c;
    -- Since $v$ is an orthonormal basis, we have $\|x\|^2 = \sum_{i=0}^{n-1} c_i^2$ and $\langle x, Ax \rangle = \sum_{i=0}^{n-1} c_i^2 \lambda_i$.
    have h_norm : dotProduct x x = ∑ i : Fin n, c i ^ 2 := by
      simp +decide [ hc.1, dotProduct, sq ];
      have h_norm : ∀ i j : Fin n, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
        intro i j; specialize hv' i; replace hv' := congr_arg ( fun x => dotProduct x ( v j ) ) hv'; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
        have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
        simpa [ mul_comm, inner ] using this i j
      generalize_proofs at *;
      -- By expanding the dot product and using the orthonormality of the basis vectors, we can simplify the expression.
      have h_expand : ∀ x y : Fin n → ℝ, (∑ i, x i • v i) ⬝ᵥ (∑ j, y j • v j) = ∑ i, x i * y i := by
        simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_comm ];
        simp_all +decide [ dotProduct ]
      generalize_proofs at *;
      convert h_expand c c using 1
    have h_inner : dotProduct x (A.mulVec x) = ∑ i : Fin n, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ := by
      -- By linearity of the inner product and the fact that $A.mulVec$ is linear, we can distribute the inner product over the sum.
      have h_inner_dist : dotProduct (∑ i, c i • v i) (A.mulVec (∑ j, c j • v j)) = ∑ i, ∑ j, c i * c j * dotProduct (v i) (A.mulVec (v j)) := by
        simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, Finset.sum_mul ];
        simp +decide only [← Finset.sum_product'];
        apply Finset.sum_bij (fun x _ => (x.2.2.2, x.2.2.1, x.1, x.2.1));
        · simp +decide;
        · aesop;
        · simp +zetaDelta at *;
        · simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
      -- Since $v$ is an orthonormal basis, we have $\langle v_i, v_j \rangle = \delta_{ij}$.
      have h_orthonormal : ∀ i j, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
        intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
        convert this i j using 1;
        simp +decide [ dotProduct, inner ];
        ac_rfl
      generalize_proofs at *;
      simp_all +decide [ pow_two, mul_assoc ];
      simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_left_comm ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, dotProduct ];
      simp [ev]
    generalize_proofs at *;
    -- Since $v$ is an orthonormal basis, we have $\lambda_i \geq \alpha_k$ for all $i \geq k$.
    have h_lambda_ge_alpha : ∀ i : Fin n, k ≤ i → ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
      simp [ev, sorted_eigenvalues_length]⟩ := by
      intros i hi
      have h_sorted : ev.get ⟨i, by
        simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
        simp [ev, sorted_eigenvalues_length]⟩ := by
        have h_sorted_list : List.Sorted (· ≤ ·) ev := by
          simpa [ev] using sorted_eigenvalues_sorted A hA
        have := List.pairwise_iff_get.mp h_sorted_list;
        grind
      generalize_proofs at *;
      exact h_sorted
    generalize_proofs at *;
    -- Since $v$ is an orthonormal basis, we have $\sum_{i=0}^{n-1} c_i^2 \lambda_i \geq \alpha_k \sum_{i=0}^{n-1} c_i^2$.
    have h_sum_ge_alpha : ∑ i : Fin n, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≥ ev.get ⟨k, by
      simp [ev, sorted_eigenvalues_length]⟩ * ∑ i : Fin n, c i ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by cases le_or_gt k i <;> [ exact by nlinarith only [ h_lambda_ge_alpha i ‹_› ] ; ; exact by rw [ hc.2 i ‹_› ] ; nlinarith only [ h_lambda_ge_alpha k le_rfl ] ] ;
    generalize_proofs at *;
    field_simp;
    rw [ rayleigh_quotient ];
    rw [ h_inner, h_norm, le_div_iff₀ ];
    · exact h_sum_ge_alpha;
    · exact h_norm ▸ lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm <| by intro H; exact hx0 <| by ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] )

/-
The k-th eigenvalue is less than or equal to the supremum of the Rayleigh quotient over any (k+1)-dimensional subspace.
-/
lemma le_sup_rayleigh_of_dim_eq_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (k : Fin n)
  (V : Submodule ℝ (Fin n → ℝ))
  (hV : Module.finrank ℝ V = k + 1) :
  (sorted_eigenvalues A hA).get ⟨k, by rw [sorted_eigenvalues_length]; exact k.isLt⟩ ≤ ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
    -- Let U be the span of eigenvectors v_k, ..., v_{n-1}.
    set U : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range (fun i : {j : Fin n // k ≤ j} => (Classical.choose (exists_orthonormal_basis_sorted A hA)) i));
    -- Since $V$ is $k+1$-dimensional and $U$ is $n-k$-dimensional, their intersection $U \cap V$ has dimension at least $1$.
    have h_inter : Module.finrank ℝ (↥(U ⊓ V)) ≥ 1 := by
      have h_inter : Module.finrank ℝ U = n - k := by
        rw [ @finrank_span_eq_card ];
        · rw [ Fintype.card_subtype ];
          rw [ show ( Finset.univ.filter fun x : Fin n => k ≤ x ) = Finset.Ici k by ext; simp +decide ] ; simp +decide;
        · refine' LinearIndependent.comp _ _ _;
          · exact ( Classical.choose ( exists_orthonormal_basis_sorted A hA ) ).orthonormal.linearIndependent;
          · exact Subtype.coe_injective;
      have h_inter : Module.finrank ℝ (↥(U ⊔ V)) ≤ n := by
        exact le_trans ( Submodule.finrank_le _ ) ( by simp );
      have := Submodule.finrank_sup_add_finrank_inf_eq U V;
      linarith [ Nat.sub_add_cancel ( show ( k : ℕ ) ≤ n from k.2.le ) ];
    -- Let $x$ be a nonzero vector in $U \cap V$.
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ≠ 0 ∧ x ∈ U ⊓ V := by
      contrapose! h_inter;
      rw [ show U ⊓ V = ⊥ from eq_bot_iff.mpr fun x hx => Classical.not_not.1 fun hx' => h_inter x hx' hx ] ; norm_num;
    refine' le_trans _ ( le_ciSup _ ⟨ ⟨ x, by aesop ⟩, by aesop ⟩ );
    · apply rayleigh_ge_of_mem_span_top A hA k (Classical.choose (exists_orthonormal_basis_sorted A hA)) (Classical.choose_spec (exists_orthonormal_basis_sorted A hA)) x;
      · exact hx.2.1;
      · exact hx.1;
    · refine' ⟨ ∑ i, ∑ j, |A i j|, Set.forall_mem_range.2 fun x => _ ⟩;
      refine' div_le_of_le_mul₀ _ _ _;
      · exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _;
      · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _;
      · -- By the properties of the dot product and the triangle inequality, we can bound the expression.
        have h_dot_product : ∀ (x : Fin n → ℝ), x ≠ 0 → |dotProduct x (A.mulVec x)| ≤ (∑ i, ∑ j, |A i j|) * dotProduct x x := by
          intros x hx_nonzero
          have h_dot_product : |dotProduct x (A.mulVec x)| ≤ ∑ i, ∑ j, |A i j| * |x i| * |x j| := by
            simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
            exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_mul ] );
          refine le_trans h_dot_product ?_;
          norm_num [ Finset.sum_mul _ _ _, mul_assoc, dotProduct ];
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( by nlinarith only [ abs_mul_abs_self ( x i ), abs_mul_abs_self ( x j ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ i ), Finset.single_le_sum ( fun i _ => mul_self_nonneg ( x i ) ) ( Finset.mem_univ j ) ] ) ( abs_nonneg _ );
        exact le_of_abs_le ( h_dot_product _ x.2 )

/-
The intersection of a subspace of dimension n-k and a subspace of dimension k+1 in an n-dimensional space is non-trivial.
-/
lemma intersection_dim_pos {n : ℕ} (k : ℕ) (U V : Submodule ℝ (Fin n → ℝ))
  (hU : Module.finrank ℝ U = n - k)
  (hV : Module.finrank ℝ V = k + 1)
  (hk : k < n) :
  ∃ x ∈ U ⊓ V, x ≠ 0 := by
    by_contra h_contra;
    have h_dim_sum : Module.finrank ℝ (↥(U ⊔ V)) = Module.finrank ℝ U + Module.finrank ℝ V := by
      rw [ ← Submodule.finrank_sup_add_finrank_inf_eq, show U ⊓ V = ⊥ from eq_bot_iff.mpr fun x hx => Classical.not_not.mp fun hx' => h_contra ⟨ x, hx, hx' ⟩ ] ; aesop;
    linarith [ Nat.sub_add_cancel hk.le, show Module.finrank ℝ ( ↥ ( U ⊔ V ) ) ≤ n from le_trans ( Submodule.finrank_le _ ) ( by simp ) ]

/-
The dimension of the span of the first k+1 eigenvectors is k+1.
-/
lemma span_bot_dim {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (_ : A.IsSymm)
  (k : Fin n)
  (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
  Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : {j : Fin n // j ≤ k} => v i))) = k + 1 := by
    rw [ finrank_span_eq_card ];
    · rw [ Fintype.card_subtype ];
      rw [ show ( Finset.filter ( fun x => x ≤ k ) Finset.univ : Finset ( Fin n ) ) = Finset.Iic k by ext; simp +decide ] ; simp +decide;
    · have := v.orthonormal;
      exact this.linearIndependent.comp _ ( by aesop_cat )

/-
Definition of a principal submatrix.
-/
def principal_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix S S ℝ :=
  A.submatrix Subtype.val Subtype.val

/-
Reindexed principal submatrix to Fin (card S).
-/
def principal_submatrix_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
  Matrix (Fin (Fintype.card {x // x ∈ S})) (Fin (Fintype.card {x // x ∈ S})) ℝ :=
  Matrix.reindex (Fintype.equivFin {x // x ∈ S}) (Fintype.equivFin {x // x ∈ S}) (principal_submatrix A S)

/-
The principal submatrix of a symmetric matrix is symmetric.
-/
lemma principal_submatrix_fin_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (S : Finset (Fin n)) :
  (principal_submatrix_fin A S).IsSymm := by
    unfold principal_submatrix_fin;
    unfold principal_submatrix; aesop;

/-
The dimension of the subspace of vectors supported on S is |S|.
-/
def subspace_of_support {n : ℕ} (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : S => (Pi.single (i : Fin n) 1 : Fin n → ℝ)))

lemma subspace_of_support_dim {n : ℕ} (S : Finset (Fin n)) :
  Module.finrank ℝ (subspace_of_support S) = S.card := by
    -- The subspace_of_support S is isomorphic to the space of functions from S to ℝ, which has dimension |S|.
    have h_iso : subspace_of_support S ≃ₗ[ℝ] (S → ℝ) := by
      -- The subspace of vectors with support in S is isomorphic to the space of functions from S to ℝ.
      have h_iso : (↥(subspace_of_support S)) ≃ₗ[ℝ] (S → ℝ) := by
        have h_subspace : subspace_of_support S = Submodule.span ℝ (Set.range (fun i : S => fun j : Fin n => if j = i then 1 else 0)) := by
          ext x; simp [subspace_of_support];
          congr!;
          aesop
        rw [ h_subspace ];
        refine' ( LinearEquiv.ofFinrankEq .. );
        rw [ @finrank_span_eq_card ] <;> norm_num;
        refine' Fintype.linearIndependent_iff.2 _;
        intro g hg i; replace hg := congr_fun hg i; simp_all +decide [ Finset.sum_ite ] ;
        rw [ Finset.sum_eq_single i ] at hg <;> aesop;
      exact h_iso;
    have := h_iso.finrank_eq;
    aesop

/-
The Rayleigh quotient is bounded by the maximum eigenvalue.
-/
lemma rayleigh_le_max_eigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (x : Fin n → ℝ) (hx : x ≠ 0) (hn : n ≠ 0) :
  rayleigh_quotient A x ≤ (sorted_eigenvalues A hA).getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length A hA ] ; positivity)) := by
    classical
    set ev := sorted_eigenvalues A hA
    obtain ⟨ v, hv ⟩ := exists_orthonormal_basis_sorted A hA;
    -- Expand x in the orthonormal basis of eigenvectors provided by \`exists_orthonormal_basis_sorted\`.
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, x = ∑ i, c i • v i := by
      have := v.sum_repr x;
      exact ⟨ _, this.symm ⟩;
    -- Substitute $x = \sum c_i v_i$ into the Rayleigh quotient.
    have h_rayleigh_subst : rayleigh_quotient A x = (∑ i, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩) / (∑ i, c i ^ 2) := by
      have h_rayleigh : dotProduct x (A.mulVec x) = ∑ i, c i^2 * (ev.get ⟨i, by
        simp [ev, sorted_eigenvalues_length]⟩) := by
        have h_rayleigh : dotProduct (∑ i, c i • v i) (∑ i, c i • (ev.get ⟨i, by
          simp [ev, sorted_eigenvalues_length]⟩) • v i) = ∑ i, c i ^ 2 * ev.get ⟨i, by
          simp [ev, sorted_eigenvalues_length]⟩ := by
          have h_inner : ∀ i j : Fin n, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
            intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
            convert this i j using 1;
            simp +decide [ dotProduct, inner ];
            ac_rfl
          generalize_proofs at *;
          simp +decide [ dotProduct, Finset.sum_mul _ _ _, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, sq ];
          simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_comm ];
          simp_all +decide [ dotProduct ]
        generalize_proofs at *;
        convert h_rayleigh using 2;
        rw [ hc, Matrix.mulVec_sum ];
        exact Finset.sum_congr rfl fun i _ => by rw [ Matrix.mulVec_smul, hv ] ;
      generalize_proofs at *;
      have h_rayleigh : dotProduct x x = ∑ i, c i^2 := by
        have h_rayleigh : ∀ i j, dotProduct (v i) (v j) = if i = j then 1 else 0 := by
          intro i j; have := v.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
          convert this i j using 1;
          exact Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_comm ] ;
        have h_rayleigh : ∀ i j, dotProduct (c i • v i) (c j • v j) = c i * c j * (if i = j then 1 else 0) := by
          simp +decide [ ← h_rayleigh, mul_assoc ];
          simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ];
        have h_rayleigh : dotProduct (∑ i, c i • v i) (∑ i, c i • v i) = ∑ i, ∑ j, dotProduct (c i • v i) (c j • v j) := by
          simp +decide only [dotProduct];
          simp +decide only [← Finset.sum_comm, ← Finset.mul_sum _ _ _, ← Finset.sum_mul];
          exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_apply ] ;
        simp_all +decide [ sq ];
      unfold rayleigh_quotient; aesop;
    generalize_proofs at *;
    -- Since $\lambda_i \le \lambda_{\max}$, we have $\sum c_i^2 \lambda_i \le \lambda_{\max} \sum c_i^2$.
    have h_sum_le_max : ∑ i, c i ^ 2 * ev.get ⟨i, by
      simp [ev, sorted_eigenvalues_length]⟩ ≤ (∑ i, c i ^ 2) * ev.getLast ‹_› := by
      rw [ Finset.sum_mul _ _ _ ];
      gcongr;
      -- Since the list is sorted in non-decreasing order, the last element is the maximum.
      have h_sorted : ∀ (i j : Fin ev.length), i ≤ j → ev.get i ≤ ev.get j := by
        have h_sorted' : List.Sorted (· ≤ ·) ev := by
          simpa [ev] using sorted_eigenvalues_sorted A hA
        exact fun i j hij => h_sorted'.rel_get_of_le hij
      convert h_sorted _ _ _;
      rotate_left;
      exact ⟨ ev.length - 1, Nat.sub_lt ((List.length_pos_iff).mpr ‹_›) zero_lt_one ⟩;
      · exact Nat.le_sub_one_of_lt ( by solve_by_elim );
      · grind
    generalize_proofs at *;
    rw [ h_rayleigh_subst, div_le_iff₀ ];
    · linarith;
    · contrapose! hx;
      exact hc.trans ( Finset.sum_eq_zero fun i _ => by rw [ show c i = 0 by exact sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => sq_nonneg ( c i ) ) ( Finset.mem_univ i ) ) hx ) ( sq_nonneg ( c i ) ) ) ] ; norm_num )

/-
The largest eigenvalue of a principal submatrix of size m is at least the m-th smallest eigenvalue of the original matrix.
-/
lemma eigenvalue_interlacing_max {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
  (S : Finset (Fin n)) (hS : S.Nonempty) :
  let m := S.card
  let subA := principal_submatrix_fin A S
  let h_subA := principal_submatrix_fin_isSymm A hA S
  let evs_A := sorted_eigenvalues A hA
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ] ; aesop)) ≥ evs_A.get ⟨m - 1, by
    rw [ sorted_eigenvalues_length ];
    exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
    classical
    -- Let $V$ be the subspace of vectors supported on $S$. Its dimension is $m$.
    set V := subspace_of_support S;
    -- By the Min-Max principle, the $(m-1)$-th eigenvalue of $A$ is $\le \sup_{x \in V, x \ne 0} R_A(x)$.
    have h_min_max : (sorted_eigenvalues A hA).get ⟨S.card - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ ≤
        ⨆ (x : {x : V // x.1 ≠ 0}), rayleigh_quotient A x.1 := by
      apply le_sup_rayleigh_of_dim_eq_succ A hA ⟨S.card - 1, by
        exact lt_of_lt_of_le ( Nat.sub_lt ( Finset.card_pos.mpr hS ) zero_lt_one ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ V
      rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr hS ) ] ; exact subspace_of_support_dim S;
    -- For any $x \in V$, let $y$ be the corresponding vector in $\mathbb{R}^m$. Then $R_A(x) = R_{subA}(y)$.
    have h_rayleigh_eq : ∀ x ∈ V, x ≠ 0 → ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 ∧ rayleigh_quotient A x = rayleigh_quotient (principal_submatrix_fin A S) y := by
      intro x hx hx_ne_zero
      obtain ⟨y, hy⟩ : ∃ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, x = fun i => if h : i ∈ S then y (Fintype.equivFin {x // x ∈ S} ⟨i, h⟩) else 0 := by
        have h_span : ∀ x ∈ V, ∃ y : {x // x ∈ S} → ℝ, x = fun i => if h : i ∈ S then y ⟨i, h⟩ else 0 := by
          intro x hx
          obtain ⟨y, hy⟩ : ∃ y : {x // x ∈ S} → ℝ, x = ∑ i : {x // x ∈ S}, y i • (Pi.single (i : Fin n) 1 : Fin n → ℝ) := by
            have h_span : x ∈ Submodule.span ℝ (Set.range (fun i : {x // x ∈ S} => (Pi.single (i : Fin n) 1 : Fin n → ℝ))) := by
              exact hx;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
            obtain ⟨ c, rfl ⟩ := h_span; use fun i => c i; simp +decide [ Finsupp.sum_fintype ] ;
          use y; ext i; simp [hy];
          split_ifs <;> simp_all +decide [ Pi.single_apply ];
          · rw [ Finset.sum_eq_single ⟨ i, by assumption ⟩ ] <;> aesop;
          · exact Finset.sum_eq_zero fun x hx => if_neg <| by aesop;
        obtain ⟨ y, rfl ⟩ := h_span x hx;
        exact ⟨ fun i => y ( Fintype.equivFin { x // x ∈ S } |>.symm i ), by ext i; aesop ⟩;
      refine' ⟨ y, _, _ ⟩;
      · contrapose! hx_ne_zero; aesop;
      · unfold rayleigh_quotient;
        unfold principal_submatrix_fin;
        unfold principal_submatrix; simp +decide [ hy, Matrix.mulVec, dotProduct ] ;
        congr! 1;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · intro a ha; simp +decide [ ha ] ;
              rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
              · rw [ ← Finset.sum_coe_sort ];
                refine' Or.inl ( Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, by aesop ⟩ ) _ _ _ _ ) <;> simp +decide;
                exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
              · aesop;
          · aesop;
        · rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
          · refine' Finset.sum_bij ( fun i hi => Fintype.equivFin { x // x ∈ S } ⟨ i, hi ⟩ ) _ _ _ _ <;> simp +decide;
            · exact fun b => ⟨ _, Finset.mem_coe.mp ( Fintype.equivFin { x // x ∈ S } |>.symm b |>.2 ), by simp +decide ⟩;
            · aesop;
          · aesop;
    -- By \`rayleigh_le_max_eigenvalue\`, $R_{subA}(y) \le \lambda_{\max}(subA)$.
    have h_rayleigh_le_max : ∀ y : Fin (Fintype.card {x // x ∈ S}) → ℝ, y ≠ 0 →
        rayleigh_quotient (principal_submatrix_fin A S) y ≤
          (sorted_eigenvalues (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S)).getLast
            (List.ne_nil_of_length_pos (by
              rw [ sorted_eigenvalues_length ];
              exact Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ )) := by
      intros y hy_nonzero
      apply rayleigh_le_max_eigenvalue (principal_submatrix_fin A S) (principal_submatrix_fin_isSymm A hA S) y hy_nonzero;
      exact ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ ⟨ hS.choose, hS.choose_spec ⟩ ⟩ );
    refine le_trans h_min_max ?_;
    convert ciSup_le _;
    · simp +zetaDelta at *;
      exact ⟨ _, Submodule.subset_span ⟨ ⟨ hS.choose, hS.choose_spec ⟩, rfl ⟩, ne_of_apply_ne ( fun x => x hS.choose ) ( by simp +decide ) ⟩;
    · grind

/-
If a principal submatrix of the Huang matrix has size > 2^(n-1), its maximum eigenvalue is at least sqrt(n).
-/
lemma huang_submatrix_max_eigenvalue_ge_sqrt_n {n : ℕ} (hn : n ≠ 0)
  (S : Finset (Fin (2^n))) (hS : S.card > 2^(n-1)) :
  let subA := principal_submatrix_fin (huang_matrix_fin n) S
  let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
  let evs_sub := sorted_eigenvalues subA h_subA
  evs_sub.getLast (List.ne_nil_of_length_pos (by
  rw [ sorted_eigenvalues_length ];
  exact Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.card_pos.mp ( pos_of_gt hS ) ), Classical.choose_spec ( Finset.card_pos.mp ( pos_of_gt hS ) ) ⟩)) ≥ Real.sqrt n := by
    have h_max_eigenvalue_ge_sqrt : let m := S.card
      let subA := principal_submatrix_fin (huang_matrix_fin n) S
      let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
      let evs_sub := sorted_eigenvalues subA h_subA
      evs_sub.getLast (List.ne_nil_of_length_pos (by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      have hlen : evs_sub.length = S.card := by
        simp [evs_sub, sorted_eigenvalues_length, Fintype.card_coe]
      rw [hlen]
      exact hSpos)) ≥ (sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)).get ⟨m - 1, by
        rw [ sorted_eigenvalues_length ];
        exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hS ) ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )⟩ := by
        apply eigenvalue_interlacing_max;
        exact Finset.card_pos.mp ( pos_of_gt hS )
    have h_eigenvalues_eq_list : let evs := sorted_eigenvalues (huang_matrix_fin n) (huang_matrix_fin_isSymm n)
      evs = List.replicate (2^(n-1)) (-Real.sqrt n) ++ List.replicate (2^(n-1)) (Real.sqrt n) := by
        exact huang_eigenvalues_eq_list n hn
    simp_all +decide [ List.getElem_append ];
    exact le_trans ( by rw [ if_neg ( by omega ) ] ) h_max_eigenvalue_ge_sqrt

/-
The sum of g_val is non-zero if f has full degree.
-/
def g_val {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (if f x then -1 else 1) * chi Finset.univ x

lemma g_val_sum_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  Finset.sum Finset.univ (g_val f) ≠ 0 := by
    unfold g_val;
    -- By definition of \`g_val\`, we can rewrite it in terms of \`chi\` and \`f\`.
    have hg_val : ∑ x : Fin n → Bool, (if f x then -1 else 1) * chi Finset.univ x = -2 * ∑ x : Fin n → Bool, (if f x then 1 else 0) * chi Finset.univ x + ∑ x : Fin n → Bool, chi Finset.univ x := by
      rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;
    -- Since $\sum_{x} \chi_{Finset.univ}(x) = 0$ for $n \neq 0$, we have:
    have h_sum_chi : ∑ x : Fin n → Bool, chi Finset.univ x = 0 := by
      unfold chi;
      -- Let's simplify the sum $\sum_{x : Fin n → Bool} (-1)^{\text{card}(\{i | x i = true\})}$.
      have h_sum_simplified : ∑ x : Fin n → Bool, (-1 : ℝ) ^ (Finset.card (Finset.filter (fun i => x i) Finset.univ)) = ∏ i : Fin n, (∑ x_i : Bool, (-1 : ℝ) ^ (if x_i then 1 else 0)) := by
        rw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide;
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
        · intro a; rw [ Finset.prod_ite ] ; aesop;
      convert h_sum_simplified using 1;
      · exact Finset.sum_congr rfl fun x hx => by rcases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) with h | h <;> rw [ ← Nat.mod_add_div ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) 2 ] <;> norm_num [ pow_add, pow_mul, h ] ;
      · norm_num [ Finset.prod_eq_zero_iff ];
        rw [ zero_pow hn ];
    have := g_expectation_nonzero f h_deg hn; aesop;

/-
Definitions of the positive and negative level sets of g.
-/
def S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = 1) Finset.univ

def S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.filter (fun x => g_val f x = -1) Finset.univ

/-
S_pos and S_neg cover the whole space.
-/
lemma S_pos_union_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  S_pos f ∪ S_neg f = Finset.univ := by
    ext x; simp [S_pos, S_neg];
    unfold g_val;
    split_ifs <;> unfold chi <;> simp +decide;
    · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) <;> simp +decide [ * ];
    · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) <;> simp +decide [ * ]

/-
S_pos and S_neg are disjoint.
-/
lemma S_pos_disjoint_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) :
  Disjoint (S_pos f) (S_neg f) := by
    exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-
One of the level sets of g has size > 2^(n-1).
-/
lemma exists_large_level_set {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (S_pos f).card > 2^(n-1) ∨ (S_neg f).card > 2^(n-1) := by
    -- Since sum g_val ≠ 0, we have |S_pos| ≠ |S_neg|.
    have h_card_ne : (S_pos f).card ≠ (S_neg f).card := by
      have h_card_ne : (Finset.sum Finset.univ (g_val f)) = (S_pos f).card - (S_neg f).card := by
        -- By definition of $g_val$, we can split the sum into the sum over $S_pos$ and the sum over $S_neg$.
        have h_split_sum : Finset.sum Finset.univ (g_val f) = Finset.sum (S_pos f) (fun x => g_val f x) + Finset.sum (S_neg f) (fun x => g_val f x) := by
          rw [ ← Finset.sum_union ];
          · rw [ S_pos_union_S_neg ];
          · exact S_pos_disjoint_S_neg f;
        rw [ h_split_sum, Finset.sum_congr rfl fun x hx => show g_val f x = 1 by exact Finset.mem_filter.mp hx |>.2, Finset.sum_congr rfl fun x hx => show g_val f x = -1 by exact Finset.mem_filter.mp hx |>.2 ] ; norm_num;
        ring;
      have := g_val_sum_ne_zero f h_deg hn; aesop;
    -- Since $|S_pos| + |S_neg| = 2^n$, we have $|S_pos| + |S_neg| = 2 * 2^{n-1}$.
    have h_card_sum : (S_pos f).card + (S_neg f).card = 2 * 2 ^ (n - 1) := by
      have h_card_sum : (S_pos f).card + (S_neg f).card = (Finset.univ : Finset (Fin n → Bool)).card := by
        rw [ ← Finset.card_union_of_disjoint ( S_pos_disjoint_S_neg f ), S_pos_union_S_neg ];
      cases n <;> simp_all +decide [ pow_succ' ];
    grind

/-
Definition of the hypercube graph.
-/
def hypercube_graph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1)

lemma hypercube_graph_adj {n : ℕ} (x y : Fin n → Bool) :
  (hypercube_graph n).Adj x y ↔ (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
    simp [hypercube_graph];
    -- If x and y are not equal, then there must be at least one index where they differ. The cardinality of the set of such indices being 1 means there's exactly one difference, which implies x and y are not equal. Conversely, if the cardinality is 1, then there's exactly one difference, so x and y can't be equal.
    apply Iff.intro;
    · simp_all +decide [ eq_comm ];
    · aesop

/-
Neighbors in the hypercube graph have opposite chi values.
-/
lemma chi_univ_neighbor {n : ℕ} (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  chi Finset.univ x = -chi Finset.univ y := by
    -- Since x and y differ by exactly one bit, their parities are opposite.
    have h_parity : (Finset.filter (fun i => x i) Finset.univ).card % 2 ≠ (Finset.filter (fun i => y i) Finset.univ).card % 2 := by
      have h_parity : (Finset.filter (fun i => x i ≠ y i) Finset.univ).card = 1 := by
        exact (hypercube_graph_adj x y).mp h_adj;
      -- Since x and y differ by exactly one bit, the number of 1s in x and y differ by 1.
      have h_diff : (Finset.filter (fun i => x i = true) Finset.univ).card + (Finset.filter (fun i => y i = true) Finset.univ).card = (Finset.filter (fun i => x i ≠ y i) Finset.univ).card + 2 * (Finset.filter (fun i => x i = true ∧ y i = true) Finset.univ).card := by
        rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        rw [ Finset.card_filter ];
        rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; by_cases hi : x i <;> by_cases hj : y i <;> simp +decide [ hi, hj ] ;
      omega;
    unfold chi; aesop;

/-
g values are equal for neighbors iff f values are different.
-/
lemma g_val_neighbor_eq_iff_f_ne {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool) (h_adj : (hypercube_graph n).Adj x y) :
  g_val f x = g_val f y ↔ f x ≠ f y := by
    have h_univ_neighbor : chi Finset.univ x = -chi Finset.univ y := by
      exact chi_univ_neighbor x y h_adj;
    unfold g_val;
    cases f x <;> cases f y <;> simp +decide [ * ];
    · unfold chi at *;
      split_ifs at * <;> norm_num at *;
    · unfold chi; split_ifs <;> norm_num;

/-
For x in S_pos, the sensitivity at x equals the degree of x in the induced subgraph on S_pos.
-/
lemma sensitivity_at_x_eq_degree_in_S_pos {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_pos f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_pos f) Finset.univ).card := by
    -- Apply the lemma \`g_val_neighbor_eq_iff_f_ne\` to each neighbor \`y\` of \`x\`.
    have h_neighbor : ∀ y : Fin n → Bool, (hypercube_graph n).Adj x y → (f x ≠ f y ↔ y ∈ S_pos f) := by
      intros y hy_adj
      have h_g_eq : g_val f x = g_val f y ↔ f x ≠ f y := by
        exact g_val_neighbor_eq_iff_f_ne f x y hy_adj;
      unfold S_pos at *; aesop;
    exact congr_arg Finset.card ( Finset.ext fun y => by specialize h_neighbor y; aesop )

/-
Checking SimpleGraph.induce
-/
/-
Definition of the induced subgraph of the hypercube graph on S.
-/
def induced_hypercube_graph {n : ℕ} (S : Finset (Fin n → Bool)) : SimpleGraph {x // x ∈ S} :=
  SimpleGraph.induce (S : Set (Fin n → Bool)) (hypercube_graph n)

/-
Definition of the hypercube graph on Fin (2^n).
-/
def hypercube_graph_fin (n : ℕ) : SimpleGraph (Fin (2^n)) :=
  (hypercube_graph n).map (boolFunEquivFin n).toEmbedding

/-
Definition of the induced subgraph of the hypercube graph on S, mapped to Fin (card S).
-/
def induced_hypercube_graph_fin_card {n : ℕ} (S : Finset (Fin (2^n))) : SimpleGraph (Fin (Fintype.card {x // x ∈ S})) :=
  let G := SimpleGraph.induce (S : Set (Fin (2^n))) (hypercube_graph_fin n)
  let equiv := Fintype.equivFin {x // x ∈ S}
  G.map equiv.toEmbedding

/-
The absolute values of the reindexed Huang matrix entries correspond to the adjacency of the reindexed hypercube graph.
-/
lemma abs_huang_fin_eq_adjacency_fin {n : ℕ} (i j : Fin (2^n)) :
  |huang_matrix_fin n i j| = if (hypercube_graph_fin n).Adj i j then 1 else 0 := by
    -- Apply the result that |huang_matrix u v| = 1 if u~v else 0.
    have h_abs : ∀ u v : Fin n → Bool, |(huang_matrix n) u v| = if (hypercube_graph n).Adj u v then 1 else 0 := by
      -- By definition of $A_n$, we know that $|A_n u v| = 1$ if $u$ and $v$ are adjacent in the hypercube graph, and $|A_n u v| = 0$ otherwise.
      intros u v
      simp [abs_huang_eq_adjacency, hypercube_graph];
      by_cases h : u = v <;> simp +decide [ h, eq_comm ];
    unfold huang_matrix_fin;
    unfold hypercube_graph_fin; aesop;

/-
The entries of the principal submatrix of the Huang matrix are bounded by the adjacency matrix of the induced subgraph.
-/
lemma huang_submatrix_bounded_by_induced_adjacency {n : ℕ} (S : Finset (Fin (2^n))) (i j : Fin (Fintype.card {x // x ∈ S})) :
  |principal_submatrix_fin (huang_matrix_fin n) S i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
    unfold principal_submatrix_fin induced_hypercube_graph_fin_card;
    simp +decide [ principal_submatrix ];
    split_ifs <;> simp_all +decide [ abs_huang_fin_eq_adjacency_fin ];
    · split_ifs <;> norm_num;
    · rename_i h;
      contrapose! h;
      use (Fintype.equivFin { x // x ∈ S }).symm i, by
        exact Finset.mem_coe.mp ( Subtype.mem _ ), (Fintype.equivFin { x // x ∈ S }).symm j, by
        exact ( Fintype.equivFin { x // x ∈ S } ).symm j |>.2
      generalize_proofs at *;
      aesop

/-
For x in S_neg, the sensitivity at x equals the degree of x in the induced subgraph on S_neg.
-/
lemma sensitivity_at_x_eq_degree_in_S_neg {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : x ∈ S_neg f) :
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card =
  (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S_neg f) Finset.univ).card := by
    unfold S_neg at *;
    congr! 2;
    ext y;
    constructor <;> intro h;
    · have := chi_univ_neighbor x y h.1; unfold g_val at *; aesop;
    · have := g_val_neighbor_eq_iff_f_ne f x y h.1; aesop;

/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_ge_sqrt_degree_of_degree_eq_n {n : ℕ} (f : (Fin n → Bool) → Bool) (h_deg : degree f = n) (hn : n ≠ 0) :
  (sensitivity f : ℝ) ≥ Real.sqrt n := by
  classical
  -- Reduce to any level set with the "right" adjacency-count equality.
  have h_main :
      ∀ (S0 : Finset (Fin n → Bool)),
        (∀ x ∈ S0,
            (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ y ∈ S0) Finset.univ).card =
              (Finset.filter (fun y => (hypercube_graph n).Adj x y ∧ f x ≠ f y) Finset.univ).card) →
        S0.card > 2^(n-1) →
        (sensitivity f : ℝ) ≥ Real.sqrt n := by
    intro S0 h_eq hS0
    -- Reindex S0 to Fin (2^n).
    let S : Finset (Fin (2^n)) := S0.map (boolFunEquivFin n).toEmbedding
    have hS : S.card > 2^(n-1) := by
      simp [S, hS0]
    let subA := principal_submatrix_fin (huang_matrix_fin n) S
    let h_subA := principal_submatrix_fin_isSymm (huang_matrix_fin n) (huang_matrix_fin_isSymm n) S
    let evs_sub := sorted_eigenvalues subA h_subA

    -- Nonempty list witness for the spectral bounds.
    have hnS : Fintype.card {x // x ∈ S} ≠ 0 := by
      have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hS
      rw [Fintype.card_coe]
      exact ne_of_gt hSpos
    have h_ne : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact Nat.pos_of_ne_zero hnS

    -- Lower bound on λ_max from interlacing.
    have hpos_sub : 0 < Fintype.card {x // x ∈ S} := by
      exact Fintype.card_pos_iff.mpr
        ⟨ ⟨ Classical.choose (Finset.card_pos.mp (pos_of_gt hS)),
            Classical.choose_spec (Finset.card_pos.mp (pos_of_gt hS)) ⟩ ⟩
    have h_ne0 : evs_sub ≠ [] := by
      apply List.ne_nil_of_length_pos
      dsimp [evs_sub]
      rw [sorted_eigenvalues_length]
      exact hpos_sub
    have h_lower0 :
        Real.sqrt n ≤ evs_sub.getLast h_ne0 := by
      simpa [subA, h_subA, evs_sub, h_ne0] using
        (huang_submatrix_max_eigenvalue_ge_sqrt_n (n := n) hn S hS)
    have h_lower : Real.sqrt n ≤ evs_sub.getLast h_ne := by
      have h_eq_last :
          evs_sub.getLast h_ne0 = evs_sub.getLast h_ne := by
        exact
          (List.getLast_congr (l₁ := evs_sub) (l₂ := evs_sub)
            (h₁ := h_ne0) (h₂ := h_ne) (h₃ := rfl))
      rw [← h_eq_last]
      exact h_lower0

    -- Upper bound on λ_max by max degree of the induced graph.
    have h_adj :
        ∀ i j,
          |subA i j| ≤ if (induced_hypercube_graph_fin_card S).Adj i j then 1 else 0 := by
      intro i j
      simpa [subA] using (huang_submatrix_bounded_by_induced_adjacency (S := S) i j)
    have h_lambda_le_max :
        evs_sub.getLast h_ne ≤ (induced_hypercube_graph_fin_card S).maxDegree := by
      simpa [subA, h_subA, evs_sub, h_ne] using
        (spectral_radius_bound (A := subA) (hA := h_subA)
          (G := induced_hypercube_graph_fin_card S) h_adj hnS)

    -- Max degree of the induced graph is at most sensitivity.
    let G0 : SimpleGraph {x // x ∈ (S0 : Set (Fin n → Bool))} :=
      (hypercube_graph n).induce (S0 : Set (Fin n → Bool))
    let G1 : SimpleGraph {x // x ∈ (S : Set (Fin (2^n)))} :=
      (hypercube_graph_fin n).induce (S : Set (Fin (2^n)))
    -- Prefer the \`Subtype.fintype\` instance to avoid instance mismatch in neighbor finsets.
    letI : Fintype {x // x ∈ (S0 : Set (Fin n → Bool))} := by
      classical
      exact (Subtype.fintype (p := fun x => x ∈ (S0 : Set (Fin n → Bool))))
    let eS : {x // x ∈ (S0 : Set (Fin n → Bool))} ≃ {x // x ∈ (S : Set (Fin (2^n)))} :=
      { toFun := fun x =>
          ⟨ (boolFunEquivFin n) x.1,
            by
              have hx0 : x.1 ∈ S0 := by
                exact Finset.mem_coe.mp x.2
              show (boolFunEquivFin n) x.1 ∈ S
              exact Finset.mem_map.mpr ⟨ x.1, hx0, rfl ⟩ ⟩
        invFun := fun y =>
          ⟨ (boolFunEquivFin n).symm y.1,
            by
              have hy : y.1 ∈ S := by
                exact Finset.mem_coe.mp y.2
              rcases Finset.mem_map.mp hy with ⟨ x0, hx0, hx0eq ⟩
              have hx0eq' : (boolFunEquivFin n).symm y.1 = x0 := by
                have h := congrArg (fun z => (boolFunEquivFin n).symm z) hx0eq
                simp at h
                exact h.symm
              have hx0' : (boolFunEquivFin n).symm y.1 ∈ S0 := by
                rw [hx0eq']
                exact hx0
              exact hx0' ⟩
        left_inv := by
          intro x; ext; simp
        right_inv := by
          intro y; ext; simp }
    let iso1 : G0 ≃g G1 :=
      { toEquiv := eS
        map_rel_iff' := by
          intro a b
          -- Reduce to adjacency in the base graphs, then use the map-adj lemma.
          change (hypercube_graph_fin n).Adj (eS a).1 (eS b).1 ↔ (hypercube_graph n).Adj a.1 b.1
          simp [hypercube_graph_fin, eS] }
    let equivS := Fintype.equivFin {x // x ∈ S}
    have iso2 : G1 ≃g induced_hypercube_graph_fin_card S := by
      dsimp [induced_hypercube_graph_fin_card, G1]
      exact SimpleGraph.Iso.map equivS G1
    let iso : G0 ≃g induced_hypercube_graph_fin_card S := iso2.comp iso1

    have h_deg_le_G0 : ∀ v0 : {x // x ∈ S0}, G0.degree v0 ≤ sensitivity f := by
      intro v0
      have h_map := SimpleGraph.map_neighborFinset_induce
        (G := hypercube_graph n) (s := (S0 : Set (Fin n → Bool))) v0
      have h_card :
          (G0.neighborFinset v0).card =
            ((hypercube_graph n).neighborFinset v0 ∩ S0).card := by
        have h_card' := congrArg Finset.card h_map
        simpa [G0, Finset.card_map, Finset.toFinset_coe, -SimpleGraph.card_neighborFinset_eq_degree] using
          h_card'
      have h_filter :
          (hypercube_graph n).neighborFinset v0 ∩ S0 =
            Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ := by
        ext y
        simp [SimpleGraph.neighborFinset_eq_filter, Finset.mem_inter, Finset.mem_filter]
      have h_degree_formula :
          G0.degree v0 =
            (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
        have h_card'' :
            (G0.neighborFinset v0).card =
              (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := by
          rw [← h_filter]
          exact h_card
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact h_card''
      have h_eq' := h_eq v0.1 (by exact Finset.mem_coe.mp v0.2)
      have h_card_le :
          (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card
            ≤ sensitivity f := by
        unfold sensitivity
        have :=
          Finset.le_sup (s := Finset.univ)
            (f := fun x =>
              Finset.card
                (Finset.filter
                  (fun y =>
                    (Finset.card
                        (Finset.filter (fun i => x i ≠ y i) Finset.univ) = 1) ∧ f x ≠ f y)
                  Finset.univ))
            (by simp : (v0 : Fin n → Bool) ∈ (Finset.univ : Finset (Fin n → Bool)))
        simp [hypercube_graph_adj]
        exact this
      calc
        G0.degree v0
            = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ y ∈ S0) Finset.univ).card := h_degree_formula
        _ = (Finset.filter (fun y => (hypercube_graph n).Adj v0 y ∧ f v0 ≠ f y) Finset.univ).card := h_eq'
        _ ≤ sensitivity f := h_card_le

    have h_maxDegree_le : (induced_hypercube_graph_fin_card S).maxDegree ≤ sensitivity f := by
      refine SimpleGraph.maxDegree_le_of_forall_degree_le (G := induced_hypercube_graph_fin_card S)
        (k := sensitivity f) ?_
      intro i
      let v0 := iso.symm i
      have hdeg : (induced_hypercube_graph_fin_card S).degree i = G0.degree v0 := by
        classical
        have hcard := Fintype.card_congr (iso.mapNeighborSet v0)
        have hiso :
            (induced_hypercube_graph_fin_card S).degree (iso v0) = G0.degree v0 := by
          calc
            (induced_hypercube_graph_fin_card S).degree (iso v0) =
                Fintype.card ((induced_hypercube_graph_fin_card S).neighborSet (iso v0)) := by
                  symm
                  simpa using
                    (SimpleGraph.card_neighborSet_eq_degree
                      (G := induced_hypercube_graph_fin_card S) (v := iso v0))
            _ = Fintype.card (G0.neighborSet v0) := by
                  simpa using hcard.symm
            _ = G0.degree v0 := by
                  simpa using (SimpleGraph.card_neighborSet_eq_degree (G := G0) (v := v0))
        have hv0 : iso v0 = i := by
          -- \`iso\` is an equivalence; rewrite with \`Equiv.apply_symm_apply\`.
          simp [v0]
        have hiso' := hiso
        rw [hv0] at hiso'
        exact hiso'
      rw [hdeg]
      exact h_deg_le_G0 v0

    -- Combine the bounds.
    have h_maxDegree_le' : (induced_hypercube_graph_fin_card S).maxDegree ≤ (sensitivity f : ℕ) := h_maxDegree_le
    have h_upper : evs_sub.getLast h_ne ≤ (sensitivity f : ℝ) := by
      exact le_trans h_lambda_le_max (by exact_mod_cast h_maxDegree_le')

    exact le_trans h_lower h_upper

  -- Pick the large level set (S_pos or S_neg).
  have h_large := exists_large_level_set f h_deg hn
  cases h_large with
  | inl hpos =>
      apply h_main (S_pos f)
      · intro x hx
        simpa using (sensitivity_at_x_eq_degree_in_S_pos f x hx).symm
      · exact hpos
  | inr hneg =>
      apply h_main (S_neg f)
      · intro x hx
        simpa using (sensitivity_at_x_eq_degree_in_S_neg f x hx).symm
      · exact hneg

/-
The sensitivity of a restriction is at most the sensitivity of the original function.
-/
def restriction {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) : (Fin (Fintype.card {x // x ∈ S}) → Bool) → Bool :=
  fun y =>
    let x : Fin n → Bool := fun i =>
      if h : i ∈ S then
        y (Fintype.equivFin {j // j ∈ S} ⟨i, h⟩)
      else
        z i
    f x

lemma sensitivity_restriction_le {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (z : Fin n → Bool) :
  sensitivity (restriction f S z) ≤ sensitivity f := by
    unfold sensitivity;
    simp +decide only [Finset.sup_le_iff];
    intro x;
    simp +decide [ restriction ];
    refine' le_trans _ ( Finset.le_sup <| Finset.mem_univ <| fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i );
    refine' le_trans _ ( Finset.card_le_card _ );
    rotate_left;
    exact Finset.image ( fun y : Fin ( Fintype.card { x // x ∈ S }) → Bool => fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ( Finset.filter ( fun y => Finset.card ( Finset.filter ( fun i => ¬x i = y i ) Finset.univ ) = 1 ∧ ¬f ( fun i => if h : i ∈ S then x ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) = f ( fun i => if h : i ∈ S then y ( Fintype.equivFin _ ⟨ i, h ⟩ ) else z i ) ) ( Finset.univ : Finset ( Fin ( Fintype.card { x // x ∈ S }) → Bool ) ) );
    · simp +decide [ Finset.subset_iff ];
      rintro _ y hy₁ hy₂ rfl; simp_all +decide [ Finset.card_eq_one ] ;
      obtain ⟨ a, ha ⟩ := hy₁; use ( Fintype.equivFin { x // x ∈ S } ).symm a; ext i; by_cases hi : i ∈ S <;> simp_all +decide [ Finset.ext_iff ] ;
      · aesop;
      · intro H; have := ha a; simp_all +decide [ Fin.ext_iff ] ;
    · rw [ Finset.card_image_of_injective ];
      intro y₁ y₂ hy; ext i; replace hy := congr_fun hy ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;

/-
The Fourier coefficient of f at S is the average of the Fourier coefficients of the restrictions at univ.
-/
lemma fourier_coeff_restriction_avg {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
  fourier_coeff f S = (Finset.sum Finset.univ (fun z => fourier_coeff (restriction f S z) Finset.univ)) / 2^n := by
    unfold fourier_coeff;
    -- Let's simplify the expression using the definition of \`restriction\`.
    have h_restrict : ∀ z : Fin n → Bool, (∑ x : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool, (if (restriction f S z x) then 1 else 0) * chi Finset.univ x) = (∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0)) := by
      intro z;
      have h_restrict : Finset.sum (Finset.univ.image (fun y : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool => fun i => if h : i ∈ S then y (Fintype.equivFin {x : Fin n // x ∈ S} ⟨i, h⟩) else z i)) (fun x => (if f x then 1 else 0) * (chi S x)) = Finset.sum (Finset.univ : Finset (Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool)) (fun y => (if (restriction f S z y) then 1 else 0) * (chi Finset.univ y)) := by
        rw [ Finset.sum_image ];
        · refine' Finset.sum_congr rfl fun y hy => _;
          unfold chi restriction; simp +decide ;
          rw [ Finset.card_filter ];
          rw [ ← Finset.sum_attach ];
          rw [ Finset.card_filter ];
          rw [ ← Equiv.sum_comp ( Fintype.equivFin { x // x ∈ S } ) ] ; aesop;
        · intro y hy y' hy' h_eq;
          ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
      rw [ ← h_restrict, Finset.sum_image ];
      · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun y : Fin ( Fintype.card { x // x ∈ S } ) → Bool => fun i => if h : i ∈ S then y ( Fintype.equivFin { x // x ∈ S } ⟨ i, h ⟩ ) else z i ) Finset.univ ) ) ];
        · rw [ Finset.sum_image ];
          · exact Finset.sum_congr rfl fun x hx => by aesop;
          · intro y₁ hy₁ y₂ hy₂ h_eq; ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
        · simp +zetaDelta at *;
          intro x hx₁ hx₂ hx₃; specialize hx₁ ( fun i => x ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ) ; simp_all +decide [ funext_iff ] ;
      · intro y₁ hy₁ y₂ hy₂ h_eq; ext i; replace h_eq := congr_fun h_eq ( Fintype.equivFin { x // x ∈ S } |>.symm i ) ; aesop;
    have h_restrict : ∀ x : Fin n → Bool, ∑ z : Fin n → Bool, (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0) = 2 ^ (Finset.card S) := by
      intros x
      have h_restrict : Finset.card (Finset.filter (fun z : Fin n → Bool => ∀ i ∈ Sᶜ, x i = z i) Finset.univ) = 2 ^ (Finset.card S) := by
        have h_restrict : Finset.card (Finset.image (fun z : Fin n → Bool => fun i : S => z i) (Finset.filter (fun z : Fin n → Bool => ∀ i ∈ Sᶜ, x i = z i) Finset.univ)) = 2 ^ (Finset.card S) := by
          rw [ show ( Finset.image ( fun z : Fin n → Bool => fun i : S => z i ) { z : Fin n → Bool | ∀ i ∈ Sᶜ, x i = z i } ) = Finset.univ from ?_ ];
          · simp +decide [ Finset.card_univ ];
          · ext z; simp [Finset.mem_image];
            use fun i => if hi : i ∈ S then z ⟨ i, hi ⟩ else x i; aesop;
        rw [ ← h_restrict, Finset.card_image_of_injOn ];
        intros z hz z' hz' h_eq;
        simp +zetaDelta at *;
        ext i; by_cases hi : i ∈ S <;> simp_all +decide [ funext_iff ] ;
      aesop;
    have h_restrict : ∑ z : Fin n → Bool, ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * (if ∀ i ∈ Sᶜ, x i = z i then 1 else 0) = ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * 2 ^ (Finset.card S) := by
      rw [ Finset.sum_comm ];
      simp +decide only [← Finset.mul_sum _ _ _, ← Finset.sum_mul];
      rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by aesop;
    have h_restrict : ∑ z : Fin n → Bool, ∑ x : Fin (Fintype.card {x : Fin n // x ∈ S}) → Bool, (if (restriction f S z x) then 1 else 0) * chi Finset.univ x = ∑ x : Fin n → Bool, (if f x then 1 else 0) * (chi S x) * 2 ^ (Finset.card S) := by
      rw [ ← h_restrict, Finset.sum_congr rfl fun _ _ => ‹∀ z : Fin n → Bool, ∑ x : Fin ( Fintype.card { x // x ∈ S } ) → Bool, ( if restriction f S z x = true then 1 else 0 ) * chi Finset.univ x = ∑ x : Fin n → Bool, ( if f x = true then 1 else 0 ) * chi S x * if ∀ i ∈ Sᶜ, x i = z i then 1 else 0› _ ];
    rw [ ← Finset.sum_div _ _ _ ];
    rw [ h_restrict, ← Finset.sum_mul _ _ _ ];
    norm_num [ Fintype.card_subtype ]

/-
If the Fourier coefficient at S is non-zero, there is a restriction with non-zero Fourier coefficient at univ.
-/
lemma exists_restriction_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : fourier_coeff f S ≠ 0) :
  ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
    rw [ fourier_coeff_restriction_avg ] at hS;
    exact not_forall.mp fun h => hS <| by rw [ Finset.sum_eq_zero fun _ _ => h _ ] ; norm_num;

/-
If the Fourier coefficient at univ is non-zero, the degree is n.
-/
lemma degree_eq_n_of_fourier_coeff_univ_ne_zero {n : ℕ} (f : (Fin n → Bool) → Bool) (h : fourier_coeff f Finset.univ ≠ 0) :
  degree f = n := by
    refine' le_antisymm _ _;
    · exact Finset.sup_le fun S hS => Nat.le_trans ( Finset.card_le_univ _ ) ( by norm_num );
    · refine' le_trans _ ( Finset.le_sup <| Finset.mem_filter.mpr ⟨ Finset.mem_univ Finset.univ, h ⟩ );
      norm_num

/-
A boolean function of degree n has sensitivity at least sqrt(n).
-/
theorem sensitivity_conjecture {n : ℕ} (f : (Fin n → Bool) → Bool) :
  (sensitivity f : ℝ) ≥ Real.sqrt (degree f) := by
    cases eq_or_ne ( degree f ) 0 <;> simp_all +decide;
    -- Let k = degree f. There exists a set S with |S| = k and f_hat(S) ≠ 0.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = degree f ∧ ∃ S : Finset (Fin n), S.card = k ∧ fourier_coeff f S ≠ 0 := by
      unfold degree at *;
      -- Since the set of S where fourier_coeff f S is non-zero is finite, it must have a maximum element in terms of cardinality.
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), fourier_coeff f S ≠ 0 ∧ ∀ T : Finset (Fin n), fourier_coeff f T ≠ 0 → T.card ≤ S.card := by
        have h_finite : Set.Finite {S : Finset (Fin n) | fourier_coeff f S ≠ 0} := by
          exact Set.toFinite _;
        apply_rules [ Set.exists_max_image ];
        contrapose! h_finite; aesop;
      refine' ⟨ _, rfl, S, _, hS.1 ⟩;
      refine' le_antisymm _ _;
      · exact Finset.le_sup ( f := Finset.card ) ( by aesop );
      · aesop;
    -- By \`exists_restriction_fourier_coeff_univ_ne_zero\`, there exists z such that the restriction g = restriction f S z has g_hat(univ) ≠ 0.
    obtain ⟨S, hS_card, hS_fourier⟩ := hk.2
    obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, fourier_coeff (restriction f S z) Finset.univ ≠ 0 := by
      exact exists_restriction_fourier_coeff_univ_ne_zero f S hS_fourier
    -- By \`degree_eq_n_of_fourier_coeff_univ_ne_zero\`, degree g = k.
    have h_deg_g : degree (restriction f S z) = S.card := by
      have := degree_eq_n_of_fourier_coeff_univ_ne_zero ( restriction f S z ) hz; aesop;
    -- By \`sensitivity_ge_sqrt_degree_of_degree_eq_n\`, sensitivity g ≥ √k.
    have h_sens_g : (sensitivity (restriction f S z) : ℝ) ≥ Real.sqrt (degree (restriction f S z)) := by
      have := sensitivity_ge_sqrt_degree_of_degree_eq_n ( restriction f S z ) ; aesop;
    -- By \`sensitivity_restriction_le\`, sensitivity f ≥ sensitivity g.
    have h_sens_f : (sensitivity f : ℝ) ≥ (sensitivity (restriction f S z) : ℝ) := by
      exact_mod_cast sensitivity_restriction_le f S z;
    grind
`;

// ============================================================================
// SCROLL-SYNCED LEAN PROOF SECTION
// ============================================================================

function LeanProofSection() {
  // Scroll-detected section (from IntersectionObserver)
  const [scrollSection, setScrollSection] = useState(0);
  // Hover-selected section (null means no hover override)
  const [hoveredSection, setHoveredSection] = useState<number | null>(null);
  // Whether mouse is currently over the code container
  const [isMouseOverCode, setIsMouseOverCode] = useState(false);

  // Active section: prioritize hover if set, otherwise use scroll
  // hoveredSection persists until scroll resets it
  const activeSection = hoveredSection !== null ? hoveredSection : scrollSection;

  const sectionRefs = useRef<(HTMLDivElement | null)[]>([]);
  const codeContainerRef = useRef<HTMLDivElement>(null);
  const explanationRef = useRef<HTMLDivElement>(null);

  // Line ranges for each section in the displayed code (24 sections matching leanSections)
  // fullLeanCode has 1936 lines (0-1935), including Harmonic tactic infrastructure
  // IMPORTANT: Ranges must be CONTIGUOUS to avoid skipping sections when scrolling
  // Generated from section-config.ts - run `bun generate-section-arrays.ts` to regenerate
  const sectionLineRanges: [number, number][] = [
    [0, 280],  // 1. Core definitions
    [281, 359],  // 2. Equivalences and Huang matrix definition
    [360, 561],  // 3. Spectral preliminaries
    [562, 854],  // 4. Huang matrix reindexing and eigen-structure
    [855, 1367],  // 5. Spectral bounds and interlacing
    [1368, 1470],  // 6. Level-set combinatorics
    [1471, 1683],  // 7. Hypercube graph and adjacency bridge
    [1684, 2163],  // 8. Full-degree case (core bound)
  ];

  // Intersection observer to track which section is visible (scroll-based detection)
  // Now uses document viewport since code scrolls with page
  useEffect(() => {
    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            const index = sectionRefs.current.findIndex(ref => ref === entry.target);
            if (index !== -1) {
              setScrollSection(index);
              // Reset hover state when scroll changes the visible section
              setHoveredSection(null);
            }
          }
        });
      },
      {
        // Use document viewport (null root) since code scrolls with page
        root: null,
        // Detect when elements reach near the top of viewport
        // Account for sticky header (~180px) with top margin
        rootMargin: '-180px 0px -70% 0px',
        threshold: 0,
      }
    );

    sectionRefs.current.forEach(ref => {
      if (ref) observer.observe(ref);
    });

    return () => observer.disconnect();
  }, []);

  // Scroll explanation into view when active section changes
  useEffect(() => {
    if (explanationRef.current) {
      explanationRef.current.scrollTo({
        top: 0,
        behavior: 'smooth',
      });
    }
  }, [activeSection]);

  const currentSection = leanSections[Math.min(activeSection, leanSections.length - 1)];
  const lines = fullLeanCode.split('\n');

  // Group lines by section
  const renderCodeWithSections = () => {
    return sectionLineRanges.map((range, sectionIdx) => {
      const [start, end] = range;
      const sectionLines = lines.slice(start, end + 1);
      const isActive = sectionIdx === activeSection;

      return (
        <div
          key={sectionIdx}
          ref={el => { sectionRefs.current[sectionIdx] = el; }}
          className={`transition-all duration-300 cursor-pointer ${
            isActive ? 'bg-primer-gold/10' : 'hover:bg-stone-100'
          }`}
          data-section={sectionIdx}
          onMouseEnter={() => setHoveredSection(sectionIdx)}
        >
          {sectionLines.map((line, lineIdx) => {
            const actualLineNum = start + lineIdx + 1;
            const tokens = tokenizeLean(line);

            return (
              <div
                key={lineIdx}
                className={`px-2 hover:bg-stone-100/50 ${
                  isActive ? 'border-l-4 border-primer-gold' : 'border-l-4 border-transparent'
                }`}
              >
                <span className="inline-block w-10 text-stone-400 text-right mr-4 select-none text-xs">
                  {actualLineNum}
                </span>
                {tokens.map((token, tokenIdx) => {
                  const colorClass = {
                    keyword: 'text-purple-600 font-semibold',
                    type: 'text-blue-600',
                    function: 'text-amber-600',
                    comment: 'text-stone-400 italic',
                    string: 'text-green-600',
                    number: 'text-orange-500',
                    operator: 'text-rose-500',
                    punctuation: 'text-stone-500',
                    tactic: 'text-teal-600 font-medium',
                    text: 'text-stone-800',
                  }[token.type];

                  return (
                    <span key={tokenIdx} className={colorClass}>
                      {token.content}
                    </span>
                  );
                })}
              </div>
            );
          })}
          {sectionIdx < sectionLineRanges.length - 1 && (
            <div className="h-4 border-l-4 border-transparent" />
          )}
        </div>
      );
    });
  };

  return (
    <section className="min-h-screen pt-24 pb-16">
      <div className="max-w-7xl mx-auto px-4">
        <div className="text-center mb-8">
          <h2 className="primer-heading text-4xl text-primer-ink mb-4">
            Full Lean Formalization
          </h2>
          <p className="primer-text text-lg text-primer-accent max-w-2xl mx-auto">
            Scroll through the complete proof. Explanations update as you explore different sections.
          </p>
        </div>

        {/* Proof Structure Summary - moved to top */}
        <div className="mb-8 bg-primer-gold-light p-6 rounded-lg">
          <h4 className="primer-heading text-lg mb-4">Proof Structure Summary</h4>
          <div className="grid md:grid-cols-3 gap-6 text-sm">
            <div>
              <h5 className="font-bold text-primer-accent mb-2">Definitions</h5>
              <ul className="space-y-1 text-stone-700">
                <li>• sensitivity — max flip count</li>
                <li>• chi — parity character</li>
                <li>• fourier_coeff & degree</li>
                <li>• huang_matrix — signed adjacency</li>
              </ul>
            </div>
            <div>
              <h5 className="font-bold text-primer-accent mb-2">Spectral Theory</h5>
              <ul className="space-y-1 text-stone-700">
                <li>• A² = nI</li>
                <li>• Eigenvalues: ±√n</li>
                <li>• Interlacing theorem</li>
                <li>• Spectral radius bound</li>
              </ul>
            </div>
            <div>
              <h5 className="font-bold text-primer-accent mb-2">Combinatorics</h5>
              <ul className="space-y-1 text-stone-700">
                <li>• g-transform & level sets</li>
                <li>• Parity flip on edges</li>
                <li>• Degree = sensitivity in S</li>
                <li>• Restriction monotonicity</li>
              </ul>
            </div>
          </div>
        </div>

        {/* Sticky progress indicator */}
        <div className="sticky top-16 z-20 bg-primer-paper py-4 -mx-4 px-4 border-b border-stone-200 shadow-sm">
          <div className="flex gap-1 flex-wrap justify-center mb-2">
            {leanSections.map((section, idx) => (
              <button
                key={idx}
                onClick={() => {
                  const ref = sectionRefs.current[idx];
                  if (ref) {
                    ref.scrollIntoView({ behavior: 'smooth', block: 'start' });
                  }
                }}
                className={`px-2 py-1 text-xs rounded transition-all ${
                  idx === activeSection
                    ? 'bg-primer-gold text-white'
                    : idx < activeSection
                    ? 'bg-cube-positive/20 text-cube-positive'
                    : 'bg-stone-200 text-stone-600 hover:bg-stone-300'
                }`}
                title={section.title}
              >
                {idx + 1}
              </button>
            ))}
          </div>
          <div className="w-full bg-stone-200 rounded-full h-1.5">
            <div
              className="bg-primer-gold h-1.5 rounded-full transition-all duration-300"
              style={{ width: `${((activeSection + 1) / leanSections.length) * 100}%` }}
            />
          </div>
        </div>

        {/* Main content: side-by-side on desktop, stacked on mobile */}
        <div className="flex flex-col lg:flex-row gap-4 mt-6">
          {/* Code panel - inline with page scroll */}
          <div
            ref={codeContainerRef}
            className="lg:w-[70%] min-w-0 overflow-hidden"
            onMouseEnter={() => setIsMouseOverCode(true)}
            onMouseLeave={() => setIsMouseOverCode(false)}
          >
            <div className="bg-stone-50 rounded-lg border border-stone-200 overflow-x-auto">
              <pre className="text-xs font-mono leading-relaxed p-3 whitespace-pre min-w-0">
                {renderCodeWithSections()}
              </pre>
            </div>
          </div>

          {/* Explanation panel - sticky on desktop, below the progress bar */}
          <div
            ref={explanationRef}
            className="lg:w-[30%] lg:sticky lg:top-36 lg:max-h-[calc(100vh-10rem)] lg:overflow-y-auto"
          >
            <div className="bg-white rounded-lg primer-border p-6 shadow-lg">
              {/* Section number badge */}
              <div className="flex items-center gap-3 mb-4">
                <span className="w-10 h-10 rounded-full bg-primer-gold text-white flex items-center justify-center font-bold">
                  {activeSection + 1}
                </span>
                <span className="text-xs text-stone-500 uppercase tracking-wide">
                  Section {activeSection + 1} of {leanSections.length}
                </span>
              </div>

              {/* Title */}
              <h3 className="primer-heading text-2xl text-primer-ink mb-3">
                {currentSection.title}
              </h3>

              {/* Description */}
              <p className="primer-text text-stone-700 mb-4 leading-relaxed">
                {currentSection.description}
              </p>

              {/* MDX Content - inlined */}
              <MDXContent
                content={sectionContent[currentSection.sectionNumber] || 'Loading...'}
                className="text-stone-800"
              />

              {/* Line reference */}
              <div className="mt-4 pt-4 border-t border-stone-200 text-xs text-stone-500">
                Lines {(sectionLineRanges[activeSection]?.[0] ?? 0) + 1}–{(sectionLineRanges[activeSection]?.[1] ?? 0) + 1}
              </div>

              {/* Navigation hint */}
              <div className="mt-6 pt-4 border-t border-stone-200 text-sm text-stone-500">
                <p>Scroll the code panel to explore, or click the section numbers above.</p>
              </div>
            </div>

            {/* Quick navigation for mobile */}
            <div className="lg:hidden flex gap-2 mt-4">
              <button
                onClick={() => {
                  const prev = Math.max(0, activeSection - 1);
                  sectionRefs.current[prev]?.scrollIntoView({ behavior: 'smooth', block: 'center' });
                }}
                disabled={activeSection === 0}
                className={`flex-1 py-2 rounded-lg font-semibold ${
                  activeSection === 0
                    ? 'bg-stone-300 text-stone-500'
                    : 'bg-primer-ink text-white'
                }`}
              >
                ← Previous
              </button>
              <button
                onClick={() => {
                  const next = Math.min(leanSections.length - 1, activeSection + 1);
                  sectionRefs.current[next]?.scrollIntoView({ behavior: 'smooth', block: 'center' });
                }}
                disabled={activeSection === leanSections.length - 1}
                className={`flex-1 py-2 rounded-lg font-semibold ${
                  activeSection === leanSections.length - 1
                    ? 'bg-stone-300 text-stone-500'
                    : 'bg-primer-ink text-white'
                }`}
              >
                Next →
              </button>
            </div>

            {/* Completion celebration */}
            {activeSection === leanSections.length - 1 && (
              <div className="mt-6 bg-primer-accent text-white p-6 rounded-lg text-center">
                <h4 className="text-xl font-bold mb-2">Proof Complete!</h4>
                <div className="my-4">
                  <Latex display>{"s(f) \\geq \\sqrt{\\deg(f)} \\quad \\blacksquare"}</Latex>
                </div>
                <p className="text-sm opacity-90">
                  You've explored the complete Lean formalization of the Sensitivity Conjecture.
                </p>
              </div>
            )}
          </div>
        </div>

      </div>
    </section>
  );
}

// ============================================================================
// MAIN APP
// ============================================================================

function App() {
  const [section, setSection] = useState<Section>("intro");

  const renderSection = () => {
    switch (section) {
      case "intro": return <IntroSection />;
      case "cube": return <CubeSection />;
      case "sensitivity": return <SensitivitySection />;
      case "fourier": return <FourierSection />;
      case "gTransform": return <GTransformSection />;
      case "huang": return <HuangSection />;
      case "spectral": return <SpectralSection />;
      case "proof": return <ProofSection />;
      case "leanProof": return <LeanProofSection />;
    }
  };

  const sections: Section[] = ["intro", "cube", "sensitivity", "fourier", "gTransform", "huang", "spectral", "proof", "leanProof"];
  const currentIdx = sections.indexOf(section);

  return (
    <div className="min-h-screen bg-primer-paper">
      <Navigation currentSection={section} setSection={setSection} />
      {renderSection()}

      <div className="max-w-4xl mx-auto px-4 pb-16 flex justify-between">
        <button
          onClick={() => {
            if (currentIdx > 0) setSection(sections[currentIdx - 1]);
          }}
          className={`px-8 py-4 rounded-lg text-lg font-semibold transition-all shadow-md ${
            section === "intro"
              ? "bg-stone-300 text-stone-500 cursor-not-allowed"
              : "bg-primer-ink text-white hover:bg-primer-accent"
          }`}
          disabled={section === "intro"}
        >
          ← Previous
        </button>
        <button
          onClick={() => {
            if (currentIdx < sections.length - 1) setSection(sections[currentIdx + 1]);
          }}
          className={`px-8 py-4 rounded-lg text-lg font-semibold transition-all shadow-md ${
            section === "leanProof"
              ? "bg-stone-300 text-stone-500 cursor-not-allowed"
              : "bg-primer-ink text-white hover:bg-primer-accent"
          }`}
          disabled={section === "leanProof"}
        >
          Next →
        </button>
      </div>
    </div>
  );
}

// ============================================================================
// RENDER
// ============================================================================

const root = createRoot(document.getElementById("root")!);
root.render(<App />);
